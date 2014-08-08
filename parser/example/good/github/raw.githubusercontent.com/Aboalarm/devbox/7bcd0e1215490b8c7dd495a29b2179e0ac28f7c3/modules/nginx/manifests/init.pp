class nginx::pkg {
  exec { 'nginx-apt-get-update':
    command => '/usr/bin/apt-get update',
    refreshonly => true,
  }

  $packages = [ 'nginx', 'nginx-extras' ]

  package { $packages:
    ensure => installed,
  }
}

class nginx::conf {
  File {
    require => Class['nginx::pkg'],
    notify => Class['nginx::service'],
    owner => 'root',
    group => 'root',
    mode => 644
  }

  file { '/etc/nginx/nginx.conf':
    source => 'puppet:///modules/nginx/nginx.conf'
  }


 file { '/usr/share/nginx/certs':
    path => '/usr/share/nginx/certs',
    ensure => directory,
    owner => root,
    group => root,
    purge => true,
    recurse => true,
    source => "puppet:///modules/nginx/certs",
  }


  file { 'nginx/sites-available':
    path => '/etc/nginx/sites-available',
    ensure => directory,
    owner => root,
    group => root,
    purge => true,
    recurse => true,
    source => "puppet:///modules/nginx/sites-available",
  }

  file { '/etc/nginx/sites-enabled/default':
    ensure => 'link',
    target => '/etc/nginx/sites-available/default'
  }

  file { '/etc/nginx/sites-enabled/laravel.dev':
    ensure => 'link',
    target => '/etc/nginx/sites-available/laravel.dev'
  }

  file { '/etc/nginx/sites-enabled/laravel.dev.ssl':
    ensure => 'link',
    target => '/etc/nginx/sites-available/laravel.dev.ssl'
  }

  file { 'var/www':
    path => '/var/www',
    ensure => directory,
    owner => vagrant,
    group => vagrant,
  }


}

class nginx::service {
  service { 'nginx':
    ensure => running,
    enable => true,
    require => Class['nginx::conf'],
  }
}

class nginx {
  include nginx::pkg, nginx::conf, nginx::service
}
