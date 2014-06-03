class ruby::service {

  service { $ruby::params::app_name:
    ensure => running,
    provider => upstart,
    require => [ Class[Ruby::Install], Class[Ruby::Config], Class[Ruby::Deps] ],
  }

}
