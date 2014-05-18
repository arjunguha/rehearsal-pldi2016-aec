class jetty::service {

  service { $jetty::params::app_name:
    ensure => running,
    provider => upstart,
    require => [ Class[Jetty::Install], Class[Jetty::Config], Class[Jetty::Deps] ],
  }

}
