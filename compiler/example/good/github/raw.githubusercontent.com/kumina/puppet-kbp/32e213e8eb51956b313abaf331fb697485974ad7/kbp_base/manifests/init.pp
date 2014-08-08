# Author: Kumina bv <support@kumina.nl>

# Class: kbp_base
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_base {
  include gen_base::reportbug
  include kbp_puppet::default_config
  include kbp_base::wanted_packages
  include gen_cron
  include kbp_acpi
  include kbp_apt
  include kbp_apt::kumina
  include kbp_ferm
  include kbp_icinga::client
  include kbp_icinga::doublemount
  include kbp_icinga::rbl
  include kbp_nagios::nrpe
  include kbp_puppet
  include kbp_ssh
  include kbp_sysctl
  include kbp_time
  include kbp_logrotate
  include kbp_user::admin_users
  include kbp_vim
  include lvm
  include sysctl
  # Needed for 'host'
  if $lsbdistcodename == 'wheezy' {
    include gen_base::libisccc80
  } else {
    include gen_base::libisccc60
  }
  # the is_virtual fact contains a STRING! Not a boolean!
  if $is_virtual == "true" {
    package { "mpt-status":
      ensure => absent;
    }
  }
  else {
    include kbp_physical
  }
  # Needed by elinks on squeeze and older
  if $lsbdistcodename != 'wheezy' {
    include gen_base::libmozjs2d
  }
  if $lsbdistcodename != 'lenny' {
    # Needed by grub2
    include gen_base::libfreetype6
  }

  kbp_mail { 'mail':; }

  kbp_ksplice { "ksplice":
    ensure => $lsbdistcodename ? {
      default  => 'present',
    };
  }

  kbp_syslog { "syslog":; }

  kbp_backup::client { "backup":; }

  kbp_ansible::client { 'ansible':; }

  gen_sudo::rule {
    "User root has total control":
      entity            => "root",
      as_user           => "ALL",
      command           => "ALL",
      password_required => true;
    "001Kumina default rule":
      entity            => "%root",
      as_user           => "ALL",
      command           => "ALL",
      password_required => true;
  }

  concat { "/etc/ssh/kumina.keys":
    owner       => "root",
    group       => "root",
    mode        => 0644,
  }

  Concat::Add_content <<| target == '/etc/ssh/kumina.keys' |>>

  # Force fsck on boot to repair the file system if it is inconsistent,
  # so we don't have to open the console and run fsck by hand
  #augeas { "/etc/default/rcS":
  #  lens    => "Shellvars.lns",
  #  incl    => "/files/etc/default/rcS",
  #  changes => "set FSCKFIX yes";
  #}

  # Add the Kumina group and users
  # XXX Needs to do a groupmod when a group with gid already exists.
  group { "kumina":
    ensure => present,
    gid => 10000,
  }

  # Set the LAST_UID in /etc/adduser.conf to 9999, so automatically created users will have a UID below 10k
  augeas { "/etc/adduser.conf":
    lens    => "Shellvars.lns",
    incl    => "/etc/adduser.conf",
    changes => "set LAST_UID 9999";
  }

  # Packages we like and want :)
  include gen_base::rsync
  package {
    ["bash","binutils","console-tools","zsh"]:
      ensure => installed;
    ["hidesvn","bash-completion","bc","tcptraceroute","diffstat","host","whois","pwgen"]:
      ensure => latest;
  }

  # We run Ksplice, so always install the latest debian kernel
  include gen_base::linux-base
  class { "gen_base::linux-image":
    version => $kernelrelease;
  }

  if versioncmp($lsbdistrelease, 6.0) < 0 {
    package { "tcptrack":
      ensure => latest,
    }
  }

  file {
    "/etc/motd.tail":
      content => template("kbp_base/motd.tail");
    "/etc/console-tools/config":
      content => template("kbp_base/console-tools/config"),
      require => Package["console-tools"];
  }

  exec {
    "uname -snrvm | tee /var/run/motd ; cat /etc/motd.tail >> /var/run/motd":
      refreshonly => true,
      path => ["/usr/bin", "/bin"],
      require => File["/etc/motd.tail"],
      subscribe => File["/etc/motd.tail"];
  }

  # kerberos 5 libs: not used explicitly, but as a dependency; always install latest
  if versioncmp($lsbdistrelease, 6) >= 0 { # Squeeze
    include gen_base::libgssapi-krb5-2
    include gen_base::libk5crypto3
    include gen_base::libkrb5-3
    include gen_base::libkrb5support0
  }

  Resolv_conf <<| title == $dcenv |>>

  if versioncmp($lsbmajdistrelease, 5) > 0 {
    # Make sure each shell can access the custenv
    file { '/etc/profile.d/custenv.sh':
      content => "export CUSTENV='${custenv}'";
    }
  } else {
    line { 'Add custenv to profile':
      file => '/etc/profile',
      content => "export CUSTENV='${custenv}'";
    }
  }
}

# Class: kbp_base::environment
#
# Parameters:
#  None.
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_base::environment {
  include kbp_icinga::environment
  include kbp_user::environment

  @@kbp_dashboard::environment { $environment:
    prettyname => $sanitized_customer_name;
  }

  @@kbp_dashboard_new::environment { $environment:
    prettyname => $sanitized_customer_name;
  }

  @@kbp_smokeping::environment { $environment:; }

  kbp_smokeping::targetgroup { $environment:; }

  @@kbp_munin::async::environment { $environment:
    prettyname => $sanitized_customer_name;
  }

  @@kbp_munin::environment { $environment:
    prettyname => $sanitized_customer_name;
  }
}

class kbp_base::wanted_packages {
  include gen_base::base-files
  include gen_base::bzip2
  include gen_base::curl
  include gen_base::dnsutils
  include gen_base::dpkg
  include gen_base::elinks
  include gen_base::file
  include gen_base::libpam0g
  include gen_base::libpam-modules
  include gen_base::libpam-runtime
  include gen_base::module_init_tools
  include gen_base::nscd
  include gen_base::perl
  include gen_base::realpath
  include gen_base::screen
  include gen_base::sysstat
  include gen_base::telnet_ssl
  include gen_base::wget
  include gen_base::htop
}

define kbp_base::resolv_conf($ns1, $ns2, $ns3=false, $domain=false, $search=$domain) {
  if ! $domain {
    fail('domain not set for resolv.conf.')
  }

  file { '/etc/resolv.conf':
    content => template('kbp_base/resolv.conf');
  }
}
