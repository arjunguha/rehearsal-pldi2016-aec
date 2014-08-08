class apache2::service {

  require apache2::params

  service {"apache2":
    ensure => running,
    name => "apache2",
    require => [ Class[Apache2::Install], Class[Apache2::Config] ],
  }

}
