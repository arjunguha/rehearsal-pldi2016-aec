group { 'puppet': ensure => 'present' }

class php54 {
  file { "/etc/apt/sources.list.d/dotdeb.list":
    ensure => file,
    owner => root,
    group => root,
    mode => 0644,
    source => "puppet:///modules/php54/dotdeb.list",
  }

  exec { 'apt-update':
    command => '/usr/bin/apt-get update',
    require => [File["/etc/apt/sources.list.d/dotdeb.list"], Exec["import-gpg"]]
  }

  exec { "import-gpg":
    command => "/usr/bin/wget -q http://www.dotdeb.org/dotdeb.gpg -O -| /usr/bin/apt-key add -"
  }

  $phpcore = ["php5", "php5-dev", "php5-cli"]
  $phpextensions = ["php5-apc", "php5-gd", "php5-xdebug", "php5-memcached", "php5-ldap", "php5-curl", "php5-mysqlnd", "php-pear"]

  package { $phpcore :
    ensure => latest,
    require => Exec["apt-update"]
  }

  package { $phpextensions :
    ensure => latest,
    require => Exec["apt-update"]
  }
}