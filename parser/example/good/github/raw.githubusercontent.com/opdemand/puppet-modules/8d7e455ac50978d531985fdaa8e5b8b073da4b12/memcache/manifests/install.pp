class memcache::install (
) {

  package {"memcached":
    ensure => latest,
  }
  
}