class nodejs::service {

  service { $nodejs::params::app_name:
    ensure => running,
    provider => upstart,
    require => [ Class[Nodejs::Install], Class[Nodejs::Config], Class[Nodejs::Deps] ],
  }

}