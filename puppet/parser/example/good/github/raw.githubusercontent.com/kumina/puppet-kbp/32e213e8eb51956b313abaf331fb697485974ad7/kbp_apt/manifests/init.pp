# Author: Kumina bv <support@kumina.nl>

# Class: kbp_apt
#
# Actions:
#  Setup APT the way we like it.
#
# Depends:
#  gen_apt
#  gen_puppet
#
class kbp_apt {
  include gen_apt

  # Keys for ksplice, jenkins, rabbitmq (in this order)
  gen_apt::key {
    "B6D4038E":
      content => template("kbp_apt/keys/B6D4038E");
    "D50582E6":
      content => template("kbp_apt/keys/D50582E6");
    "056E8E56":
      content => template("kbp_apt/keys/056E8E56");
  }

  # Config options are explained in /etc/cron.daily/apt.
  file { '/etc/apt/apt.conf.d/02periodic':
    content => "APT::Periodic::Update-Package-Lists \"1\";\nAPT::Periodic::Download-Upgradeable-Packages \"1\";\nAPT::Periodic::AutocleanInterval \"1\";\n";
  }

  kcron { 'remove-unneeded-packages':
    user        => 'root',
    environment => ['PATH=/bin:/sbin:/usr/bin:/usr/sbin','DEBIAN_FRONTEND=noninteractive'],
    mailto      => "reports+${environment}@kumina.nl",
    command     => '/usr/bin/apt-get -qq -y autoremove',
    hour        => 0,
    minute      => 0;
  }
}

# Class: kbp_apt::kumina
#
# Actions:
#  Setup the APT source for the kumina repository, including keeping the key up-to-date and making sure we always prefer
#  packages that we've packaged ourselves.
#
# Depends:
#  gen_apt
#  gen_puppet
#
class kbp_apt::kumina {
  if $lsbdistcodename == 'n/a' {
    fail('Refusing to deploy without a working lsb_release -c.')
  }

  gen_apt::key { "031687AC":
    content => template("kbp_apt/keys/031687AC");
  }

  gen_apt::source {
    "kumina":
      comment      => "Kumina repository.",
      sourcetype   => "deb",
      uri          => "http://debian.kumina.nl/debian",
      distribution => "${lsbdistcodename}-kumina",
      components   => "main",
      key          => "031687AC";
  }

  # This mustn't depend on apt-get update, as we cannot do that when an https deb source is declared and this package isn't installed
  package {
    "apt-transport-https":
      ensure  => latest;
    "kumina-archive-keyring":
      ensure => latest;
  }

  # Always prefer packages that we created ourselves.
  gen_apt::preference { "all":
    package => "*",
    prio    => '499',
    repo    => "${lsbdistcodename}-kumina";
  }
}

# Class: kbp_apt::kumina
#
# Actions:
#  Setup the APT source for the kumina repository, including keeping the key up-to-date and making sure we always prefer
#  packages that we've packaged ourselves.
#
# Depends:
#  gen_apt
#  gen_puppet
#
class kbp_apt::kumina_non_free ($repopassword = "BOGUS"){
  # Pull in the key and other stuff we need
  include kbp_apt::kumina

  gen_apt::source {
    "kumina-non-free":
      comment      => "Kumina non-free repository.",
      sourcetype   => "deb",
      uri          => "https://${environment}:${repopassword}@debian-non-free.kumina.nl/debian",
      distribution => "${lsbdistcodename}-kumina",
      components   => "non-free",
      key          => "031687AC",
      require      => Package["apt-transport-https"];
  }
}
