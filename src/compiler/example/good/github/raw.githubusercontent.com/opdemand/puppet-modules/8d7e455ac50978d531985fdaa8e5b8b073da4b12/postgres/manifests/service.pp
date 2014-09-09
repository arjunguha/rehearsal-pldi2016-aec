class postgres::service {
  
  service { "postgresql":
    ensure => running,
    enable => true,
    hasstatus => true,
    subscribe => Package["postgresql"],
  }
}