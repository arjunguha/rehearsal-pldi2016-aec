class puppet::agent {
  include puppet

  package { "puppet": provider => gem }

  case $operatingsystem {
    Darwin: {
      # Do nothing special here
    }
  
    windows: {
      # Do nothing special here
    }
  
    default: {
      file { "/etc/puppet/puppet.conf":
        owner   => root,
        group   => root,
        mode    => 0755,
        ensure  => present,
        content => template("puppet/puppet.conf.erb"),
        require => Package["puppet"];
      }
    }
  }
}
