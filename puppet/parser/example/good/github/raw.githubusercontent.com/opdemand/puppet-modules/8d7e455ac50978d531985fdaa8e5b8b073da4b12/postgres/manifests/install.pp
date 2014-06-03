class postgres::install {
  
  require postgres::params

  package { "postgresql":
    ensure => latest,
  }

  user { 'postgres':
    ensure => 'present',
    comment => 'PostgreSQL Server',
    managehome => true,
    password => '!!',
    require => Package["postgresql"],
  }

  group { 'postgres':
    ensure => 'present',
    require => Package["postgresql"],
  }
  
}
