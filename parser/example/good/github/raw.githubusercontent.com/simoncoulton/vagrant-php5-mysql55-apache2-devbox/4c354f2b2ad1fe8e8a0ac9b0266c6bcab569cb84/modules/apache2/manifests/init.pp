group { 'puppet': ensure => 'present' }

class apache2 {
  package { "apache2":
    ensure => present,
    require => Exec['apt-get update']
  }

  exec { 'enable_rewrite':
  	command => 'a2enmod rewrite',
  	require => Exec["enable_ssl"]
  }

  exec { 'enable_ssl':
  	command => 'a2enmod ssl',
  	require => Package["apache2"]
  }

  service { "apache2":
    ensure => running,
    require => Exec["enable_rewrite"],
  }
}