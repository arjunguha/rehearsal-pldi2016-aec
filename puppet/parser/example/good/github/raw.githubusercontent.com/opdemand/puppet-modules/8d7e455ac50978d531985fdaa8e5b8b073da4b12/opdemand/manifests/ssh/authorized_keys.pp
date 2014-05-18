
class opdemand::ssh::authorized_keys { 

  require opdemand::common
  require opdemand::ssh::dirs
  
  $keys = hiera("server/ssh_authorized_keys")
  
  # add a key for each in the list
  add { $keys: }
  
}

define add() {
  
  if $name =~ /^(ssh-...) ([^ ]+) ?(.+)?/ {
    
    $keytype = $1
    $modulus = $2
    $keyid = $3
       
    $keyname = $keyid ? {
      /(.+)/  => $1,
      default => "default"
    } 
    
    # add authorized keys to ubuntu user
    ssh_authorized_key { "${keyname}":
      ensure  => "present",
      user    => "ubuntu",
      type    => $keytype,
      key     => $modulus,
      options => $options ? { "" => undef, default => $options },
    }
    
  } else {
    notice('failed to parse $name')
  }
  
}