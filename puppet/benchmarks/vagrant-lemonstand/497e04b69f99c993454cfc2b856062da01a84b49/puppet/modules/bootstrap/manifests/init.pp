class bootstrap
{
  group { "puppet":
    ensure => "present",
  }

  if $virtual == "virtualbox" and $fqdn == '' {
    $fqdn = 'localhost'
  }

  exec { "apt-get update":
    command => '/usr/bin/apt-get update',
  }

  # File { owner => 0, group => 0, mode => 0644 }
  # 
  # file { '/etc/motd':
  #   content => "Welcome!\n"
  # }
}
