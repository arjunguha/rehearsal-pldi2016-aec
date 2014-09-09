class python::config {

  # local variables
  $repository_path = "$python::params::repository_path"
  $app_name = "$python::params::app_name"
  $username = "$python::params::username"
  $num_listeners = "$python::params::num_listeners"
  $env_path = "$opdemand::inputs::env_path"
  
  # rebuild upstart conf files
  exec {"rebuild-upstart":
    path => ["/sbin", "/bin", "/usr/bin", "/usr/local/bin"],
    cwd => $repository_path,
    command => "foreman export upstart /etc/init -a $app_name -u $username -e $env_path -c web=$num_listeners -t /var/cache/opdemand",
    # rebuild on change of inputs.sh or the vcsrepo
    subscribe => [ File[$env_path], Vcsrepo[$repository_path] ],
    # notify the service on change
    notify => Service[$app_name],
    require => Class[Python::Install],
  }

}