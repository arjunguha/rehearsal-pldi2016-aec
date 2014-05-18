class mysql::install {
  
  require mysql::params

  package { "mysql-server":
    ensure => latest,
  }

  user { 'mysql':
    ensure => 'present',
    comment => 'MySQL Server',
    managehome => false,
    shell => '/bin/false',
    password => '!',
    require => Package["mysql-server"],
  }

  group { 'mysql':
    ensure => 'present',
    require => Package["mysql-server"],
  }
  
}
