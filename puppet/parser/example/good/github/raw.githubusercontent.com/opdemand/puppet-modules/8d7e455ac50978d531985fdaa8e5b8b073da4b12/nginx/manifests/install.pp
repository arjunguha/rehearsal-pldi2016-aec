class nginx::install {

  # local variables
  $ppa = "ppa:nginx/stable" # use latest stable
  $packages = [ "nginx" ]
  $apache_packages = [ "apache2.2-common", "apache2.2-bin", "apache2-utils" ]
  
  # install ppa
  apt::ppa {$ppa:}
  
  # install base python packages
  package { $packages:
    ensure => latest,
    require => Apt::Ppa[$ppa],
  }

  # remove apache2 packages that may be auto-installed on ubuntu
  package { $apache_packages:
    ensure => absent,
  }
  
}
