class module2 {

  service {'networking':
    ensure => running
  }

  -> 

  package {'sl':
    ensure => present
  }
}
