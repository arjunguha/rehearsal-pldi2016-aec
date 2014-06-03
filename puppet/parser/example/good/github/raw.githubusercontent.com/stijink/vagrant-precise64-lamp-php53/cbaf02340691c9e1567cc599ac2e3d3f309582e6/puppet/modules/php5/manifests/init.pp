class php5 {

  package { "php5":
    ensure => present,
    require => Exec['apt-get update']
  }

  package { "php5-cli":
      ensure => present,
      require => [ Package['php5'], Exec['apt-get update']]
  }

  package { "php5-mysql":
      ensure => present,
      require => [ Package['php5'], Exec['apt-get update']]
  }

  package { "php5-curl":
      ensure => present,
      require => [ Package['php5'], Exec['apt-get update']]
  }

  package { "php5-xdebug":
      ensure => present,
      require => [ Package['php5'], Exec['apt-get update']]
  }

  package { "php-pear" :
      ensure => present,
      require => Package['php5'],
      notify  => Service['apache2']
  }

  package { "libapache2-mod-php5":
    ensure => present,
    require => Package['php5', 'apache2']
  }

  package { "php-apc":
      ensure => present,
      require => Package['php5', 'apache2'],
      notify  => Service['apache2']
    }

  # PHPUNIT

  exec { "pear-upgrade":
    command => "sudo pear upgrade pear",
    require => Package['php-pear']
  }

  exec { "pear-channel-discover":
    unless  => "sudo pear list-channels | grep pear.phpunit.de",
    command => "sudo pear channel-discover pear.phpunit.de; sudo pear channel-discover components.ez.no; sudo pear channel-discover pear.symfony.com",
    require => Exec['pear-upgrade']
  }

  exec { "pear-install-phpunit":
    unless  => "sudo pear list phpunit/PHPUnit | grep /usr/bin/phpunit",
    command => "sudo pear install --alldeps phpunit/PHPUnit",
    require => Exec['pear-channel-discover']
  }
}