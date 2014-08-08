class nginx::config {
  
  # local variables
  $app_name = $nginx::params::app_name
  $num_listeners = $nginx::params::num_listeners
  $template_name = $nginx::params::template_name
  $public_root = $nginx::params::public_root
  $server_name = $nginx::params::server_name
  $access_port = $nginx::params::access_port
  $start_port = $nginx::params::start_port
  
  # install sites-enabled (skip sites-available for now)
  file {"/etc/nginx/sites-enabled/$app_name":
    ensure => file,    
    owner => "root",
    group => "root",
    mode => 0644,
    content => template("nginx/$template_name.conf.erb"),
    require => Class[Nginx::Install],
    notify => Service["nginx"],
  }

  # ensure default site is removed
  file {"/etc/nginx/sites-enabled/default":
    ensure => absent,
    require => Class[Nginx::Install],
  }  
  
}
