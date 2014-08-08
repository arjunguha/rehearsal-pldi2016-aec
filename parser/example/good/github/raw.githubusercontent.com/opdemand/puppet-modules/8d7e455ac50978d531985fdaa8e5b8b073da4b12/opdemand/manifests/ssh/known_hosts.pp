
class opdemand::ssh::known_hosts { 

  require opdemand::common   
  require opdemand::ssh::dirs
  
  $host_fingerprints = hiera("server/ssh_known_hosts")
  
  # add to root known_hosts
  file { "/root/.ssh/known_hosts":
    ensure  => "present",
    owner    => "root",
    group   => "root",
    mode    => 0600,
    content => template("opdemand/known_hosts.erb"),
  }
  
  # add to ubuntu known_hosts
  file { "/home/ubuntu/.ssh/known_hosts":
    ensure  => "present",
    owner    => "ubuntu",
    group   => "ubuntu",
    mode    => 0600,
    content => template("opdemand/known_hosts.erb"),
  }
  
}
