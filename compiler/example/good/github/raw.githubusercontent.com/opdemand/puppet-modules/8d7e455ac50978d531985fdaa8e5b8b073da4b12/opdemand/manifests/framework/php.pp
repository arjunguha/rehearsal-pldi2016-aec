class opdemand::framework::php {

  # require opdemand common and repo
  require opdemand::common
  require opdemand::repo::app
  require opdemand::web::nginx
  
  # include nginx and php::nginx
  include nginx
  include php::nginx

  $packages = ["php5-cli", "php5-dev", "php5-curl", "php5-memcache", "php5-common", "php5-mysql", "php-pear", "php5-gd", "php5-imagick", "php5-imap", "php5-mcrypt", "php5-ming", "php5-ps", "php5-pspell", "php5-recode", "php5-snmp", "php5-sqlite", "php5-tidy", "php5-xsl", "php-apc"]

  # initialize dynamic parameters
  class {"php::params":
    packages => $packages,
    require => Class[Opdemand::Repo::App],
  }

  file { "/var/www":
    ensure => symlink,
    target => "$opdemand::repo::app::repository_path/public",
    force => true,
  }

  # notify nginx on repo change
  Vcsrepo["$opdemand::repo::app::repository_path"] ~> Service["nginx"]

  # include relevant classes
  include php::install
  include php::config

}
