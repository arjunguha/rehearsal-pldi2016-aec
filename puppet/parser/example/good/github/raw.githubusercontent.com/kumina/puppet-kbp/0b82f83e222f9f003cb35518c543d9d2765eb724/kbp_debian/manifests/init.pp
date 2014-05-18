# Author: Kumina bv <support@kumina.nl>

# Class: kbp_debian::etch
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_debian::etch {
}

# Class: kbp_debian::lenny
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_debian::lenny {
  include kbp_debian::oldstable
  # Don't pull in Recommends or Suggests dependencies when installing
  # packages with apt.
  file {
    "/etc/apt/apt.conf.d/no-recommends":
      content => "APT::Install-Recommends \"false\";\n";
    "/etc/apt/apt.conf.d/no-suggests":
      content => "APT::Install-Suggests \"false\";\n";
  }

  gen_apt::source {
    "${lsbdistcodename}-volatile":
      comment      => "Repository for volatile packages in $lsbdistcodename, such as SpamAssassin and Clamav",
      sourcetype   => "deb",
      uri          => "http://ftp.nl.debian.org/debian-volatile/",
      distribution => "${lsbdistcodename}/volatile",
      components   => "main";
  }

  package { "mailx":
    ensure => installed
  }

  # Package which makes sure the installed Backports.org repository key is
  # up-to-date.
  package { "debian-backports-keyring":
    ensure => installed,
  }
}

# Class: kbp_debian::squeeze
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_debian::generic {
  include gen_haveged

  # Don't pull in Recommends or Suggests dependencies when installing
  # packages with apt.
  file {
    "/etc/apt/apt.conf.d/no-recommends":
      content => "APT::Install-Recommends \"false\";\n";
    "/etc/apt/apt.conf.d/no-suggests":
      content => "APT::Install-Suggests \"false\";\n";
  }

  if $lsbdistcodename != 'wheezy' {
    gen_apt::source { "${lsbdistcodename}-updates":
      comment      => "Repository for update packages in ${lsbdistcodename}, such as SpamAssassin and Clamav",
      sourcetype   => "deb",
      uri          => "http://ftp.nl.debian.org/debian/",
      distribution => "${lsbdistcodename}-updates",
      components   => "main";
    }
  }

  package { "bsd-mailx":; }
}

# Class: kbp_debian
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_debian inherits kbp_base {
  # put default timezone files in place
  include gen_timezone

  if $lsbdistcodename == 'lenny' {
    include kbp_debian::lenny
  } else {
    include kbp_debian::generic
  }
  include rng-tools

  define check_alternatives($linkto) {
    exec { "/usr/sbin/update-alternatives --set $name $linkto":
      unless => "/bin/sh -c '[ -L /etc/alternatives/$name ] && [ /etc/alternatives/$name -ef $linkto ]'"
    }
  }

  # Packages we want to have installed
  $wantedpackages = ["openssh-server", "less", "debsums", "gnupg", "ucf", "tree", "netcat", "openssh-client", "tcpdump", "iproute", "acl", "tmux", "psmisc", "udev", "lsof", "strace", "pinfo", "lsb-release", "ethtool", "socat", "make"]
  package { $wantedpackages:
    ensure => installed;
  }

  # We do not need to backup the dlocate database
  kbp_backup::exclude { '/var/lib/dlocate/*':; }

  package { "ca-certificates":
    ensure => latest;
  }

  # Packages we do not need, thank you very much!
  $unwantedpackages = ["pidentd", "dhcp3-client", "dhcp3-common", "dictionaries-common", "doc-linux-text", "doc-debian",
    "iamerican", "ibritish", "ispell", "laptop-detect", "libident", "mpack", "mtools", "popularity-contest", "procmail", "tcsh",
    "w3m", "wamerican", "ppp", "pppoe", "pppoeconf", "at", "mdetect", "tasksel", "aptitude"]

  package { $unwantedpackages:
    ensure => purged;
  }

  if $lsbdistcodename == 'wheezy' {
    # These packages have only been tested absent on Wheezy
    package { ['aptitude-common','geoip-database','krb5-locales','os-prober','vim-tiny','xauth','isc-dhcp-client','isc-dhcp-common']:
      ensure => purged,
    }
  }

  # Ensure /tmp always has the correct permissions. (It's a common
  # mistake to forget to do a chmod 1777 /tmp when /tmp is moved to its
  # own filesystem.)
  file { "/tmp":
    mode => 1777,
  }

  service { "ssh":
    ensure => running,
    require => Package["openssh-server"],
  }

  # We want to use pinfo as infobrowser, so when the symlink is not
  # pointing towards pinfo, we need to run update-alternatives
  check_alternatives { "infobrowser":
    linkto => "/usr/bin/pinfo",
    require => Package["pinfo"]
  }

  file { "/etc/skel/.bash_profile":
    content => template("kbp_debian/skel/bash_profile");
  }

  package {
    "adduser":;
    "locales":
      require      => File["/var/cache/debconf/locales.preseed"],
      responsefile => "/var/cache/debconf/locales.preseed",
      ensure       => installed;
  }

  file {
    "/var/cache/debconf/locales.preseed":
      content => template("kbp_debian/locales.preseed");
  }

  gen_apt::source {
    "${lsbdistcodename}-base":
      comment      => "The main repository for the installed Debian release: ${lsbdistdescription}.",
      sourcetype   => "deb",
      uri          => $lsbdistcodename ? {
        'lenny' => "http://archive.debian.org/debian/",
        default => "http://ftp.nl.debian.org/debian/",
      },
      distribution => "${lsbdistcodename}",
      components   => "main contrib non-free";
    "${lsbdistcodename}-security":
      comment      => "Security updates for ${lsbdistcodename}.",
      sourcetype   => "deb",
      uri          => "http://security.debian.org/",
      distribution => "${lsbdistcodename}/updates",
      components   => "main contrib non-free";
  }

  if $lsbmajdistrelease > 6 {
    gen_apt::source { "${lsbdistcodename}-backports":
      comment      => "Repository for packages which have been backported to ${lsbdistcodename}.",
      sourcetype   => "deb",
      uri          => "http://ftp.nl.debian.org/debian/",
      distribution => "${lsbdistcodename}-backports",
      components   => "main contrib non-free";
    }
  } else {
    gen_apt::source { "${lsbdistcodename}-backports":
      comment      => "Repository for packages which have been backported to ${lsbdistcodename}.",
      sourcetype   => "deb",
      uri          => "http://backports.debian.org/debian-backports",
      distribution => "${lsbdistcodename}-backports",
      components   => "main contrib non-free";
    }
  }

  if $lsbdistcodename != 'wheezy' {
  }

  # TODO: move to appropriate modules (ticket 588)
  if $lsbdistcodename == "lenny" {
    gen_apt::preference { ["libvirt-bin","virtinst","libvirt-doc","libvirt0","virt-manager","libasound2","libbrlapi0.5","kvm","rake","python-django","varnish","linux-image-2.6-amd64","firmware-bnx2","drbd8-utils","heartbeat","python-support"]:; }
  }
}


#
# Class: kbp_debian::oldstable
#
# Actions:
#  Override some repos to use archive.debian.org
#
# Depends:
#  kbp_debian::base
#
class kbp_debian::oldstable {
  Gen_apt::Source <| title == "${lsbdistcodename}-base" |> {
      uri          => "http://archive.debian.org/debian",
  }
  Gen_apt::Source <| title ==  "${lsbdistcodename}-security" |> {
      uri          => "http://archive.debian.org/debian-security",
  }
  Gen_apt::Source <| title == "${lsbdistcodename}-backports" |> {
      uri          => "http://archive.debian.org/debian-backports",
  }
}
