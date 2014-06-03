class opdemand::inputs {

  $exec_path = "/var/cache/opdemand"
  $json_path = "$exec_path/inputs.json"
  $env_path = "$exec_path/inputs.sh"
  
  file {$json_path:
    ensure => present
  }

  file {$env_path:
    ensure => present
  }
  
  exec {"export":
    cwd => $opdemand::inputs::exec_path,
    command => "/usr/local/bin/opdemand-export",
    path => ["/sbin", "/bin", "/usr/bin", "/usr/local/bin"],
    user => "root",
    group => "root",
    require => File[$json_path],
    # trigger on change to inputs.json
    subscribe => File[$json_path],
  }
  
}