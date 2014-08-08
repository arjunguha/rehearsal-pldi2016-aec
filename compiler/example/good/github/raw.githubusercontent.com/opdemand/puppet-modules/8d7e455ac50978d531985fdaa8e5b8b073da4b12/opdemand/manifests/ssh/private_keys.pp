
class opdemand::ssh::private_keys { 

  require opdemand::common
  require opdemand::ssh::dirs
  
  $server_private_key = hiera("server/ssh_private_key", "")
  $app_private_key = hiera("application/repository_key", "")
  
  if $server_private_key {
    # add server private key to root user
    opdemand::ssh::private::add { "server":
      contents => $server_private_key,
      user => "root",
      home => "/root",
    }
  }
  
  if $app_private_key {
    # add app private key to root user
    opdemand::ssh::private::add { "root":
      contents => $app_private_key,
      user => "root",
      home => "/root",
      prefix => "opdemand",
    }
    # add app private key to ubuntu user
    opdemand::ssh::private::add { "ubuntu":
      contents => $app_private_key,
      user => "ubuntu",
      home => "/home/ubuntu",
      prefix => "opdemand",
    }
  }
  
}

define opdemand::ssh::private::add($contents,
                                   $user,
                                   $home,
                                   $prefix="id") {
  
  if $contents =~ /^-----BEGIN (...) PRIVATE KEY/ {
    
    if $prefix == "opdemand" {
      # use hardcoded key name
      $user_file_path = "$home/.ssh/opdemand-app"
    } else {
      # name key based on type
      case $1 {
        'RSA': { $user_file_path = "$home/.ssh/$prefix_rsa" }
        'DSA': { $user_file_path = "$home/.ssh/$prefix_dsa" }
      }
    }
    
    file { $user_file_path:
      owner   => $user,
      group   => $group,
      mode    => 600,
      content => $contents,
      ensure => present,
    }
    
  } else {
    notice('skipped server/ssh_private_key installation')
  }
    
}
