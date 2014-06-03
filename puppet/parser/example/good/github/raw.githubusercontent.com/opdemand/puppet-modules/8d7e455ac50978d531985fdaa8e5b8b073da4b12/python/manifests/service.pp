class python::service {

  service { $python::params::app_name:
    ensure => running,
    provider => upstart,
    require => [ Class[Python::Install], Class[Python::Config], Class[Python::Deps] ],
  }

}
