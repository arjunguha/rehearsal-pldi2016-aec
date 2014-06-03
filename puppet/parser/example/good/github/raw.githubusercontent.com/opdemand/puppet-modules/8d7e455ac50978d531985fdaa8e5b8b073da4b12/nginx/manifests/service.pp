class nginx::service {

  # local variables
  $app_name = $nginx::params::app_name
  
  service { "nginx":
    ensure => running,
    require => [ Class[Nginx::Install], Class[Nginx::Config] ],
    subscribe => Service[$app_name],
  }

}
