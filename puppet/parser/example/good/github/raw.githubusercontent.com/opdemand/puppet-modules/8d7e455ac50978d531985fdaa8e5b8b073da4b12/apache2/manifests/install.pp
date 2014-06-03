class apache2::install {
 
  require apache2::params

  $packages = $apache2::params::mpm ? {
    prefork => [ "apache2", "apache2-mpm-prefork" ],
    worker => [ "apache2", "apache2-mpm-worker" ],
  }

  package { $packages:
    ensure => latest,
  }

}

