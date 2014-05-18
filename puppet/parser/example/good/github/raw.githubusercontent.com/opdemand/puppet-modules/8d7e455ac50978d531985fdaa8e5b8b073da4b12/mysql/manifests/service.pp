class mysql::service {
  
  service { "mysql":
    ensure => running,
    enable => true,
    hasstatus => true,
    subscribe => Package["mysql-server"],
  }
  
}