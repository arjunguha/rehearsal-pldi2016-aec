define ceilometer::upstart ($enabled) {
  Ceilometer_config<||> ~> Service["${name}-service"]

  file {"${name}-upstart-link":
    name   => "/etc/init.d/${name}",
    ensure => link,
    target => '/lib/init/upstart-job'
  }

  file {"${name}-upstart":
    name    => "/etc/init/${name}.conf",
    ensure  => present,
    owner   => root,
    group   => root,
    content => template('ceilometer/upstart.erb'),
    require => [File["${name}-upstart-link"], Vcsrepo['ceilometer']]
  }

  if ($enabled) {
    $service_ensure = 'running'
  } else {
    $service_ensure = 'stopped'
  }

  service {"${name}-service":
    name      => $name,
    ensure    => $service_ensure,
    enable    => $enabled,
    provider  => upstart,
    require   => File["${name}-upstart"],
  }
}
