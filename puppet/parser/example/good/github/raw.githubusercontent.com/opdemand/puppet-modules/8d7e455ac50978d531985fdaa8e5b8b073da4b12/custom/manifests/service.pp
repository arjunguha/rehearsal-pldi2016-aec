class custom::service {

  service { $custom::params::app_name:
    ensure => running,
    provider => upstart,
    require => [ Class[Custom::Install], Class[Custom::Config], Class[Custom::Deps] ],
  }

}