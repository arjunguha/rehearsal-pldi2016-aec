user {'foo':
  managehome => true
}

file {'/usr/local/settings':
  ensure => present
}
