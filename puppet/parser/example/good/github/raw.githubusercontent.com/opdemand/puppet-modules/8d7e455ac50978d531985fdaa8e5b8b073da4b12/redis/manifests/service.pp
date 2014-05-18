class redis::service {
  
  service {"redis-server":
    ensure    => running,
    hasstatus => true,
    enable    => true,
    require   => [Package["redis-server"]],
    subscribe => File["/etc/redis/redis.conf"],
  }
    
}
