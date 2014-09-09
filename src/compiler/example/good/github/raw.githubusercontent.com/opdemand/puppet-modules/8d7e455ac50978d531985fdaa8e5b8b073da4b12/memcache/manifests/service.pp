class memcache::service {
  
  service {"memcached":
    ensure    => running,
    hasstatus => true,
    enable    => true,
    require   => Class[Memcache::Config],
    subscribe => File["/etc/memcached.conf"],
  }
    
}
