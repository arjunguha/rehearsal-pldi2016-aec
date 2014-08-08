#
# Class: kbp_redis::server
#
# Actions: Install and set up redis-server.
#
# Parameters:
#  bind_address: The address to bind to
#  datadir: The directory where the redis data is stored
#  redis_tag: The tag for this redis instance
#  memory_limit: Max amount of memory to use before starting to respond badly to SET queries, in bytes, defaults to false to disable this option
#  appendonly: Enable appendonly mode, defaults to false to disable.
#
# Depends:
#  gen_redis
#  kbp_ferm
#
class kbp_redis::server ($bind_address='127.0.0.1', $datadir='/srv/redis', $redis_tag=false, $memory_limit=false, $appendonly=false) {
  class { 'gen_redis':
    bind_address => $bind_address,
    memory_limit => $memory_limit,
    appendonly   => $appendonly,
    datadir      => $datadir;
  }

  kbp_icinga::proc_status { 'redis-server':; }

  $redis_ferm_tag= $redis_tag ? {
    false   => "${environment}_${dcenv}_redis",
    default => "${environment}_${dcenv}_redis_${redis_tag}",
  }

  Kbp_ferm::Rule <<| tag == $redis_ferm_tag |>>

  # Required according to the Redis documentation
  sysctl::setting { 'vm.overcommit': value => 1; }
}

#
# Class: kbp_redis::client
#
# Actions: Export firewall rules for the redis servers
#
# Parameters:
#  redis_tag: The tag for this redis instance
#
# Depends:
#  kbp_ferm
#
class kbp_redis::client ($saddr, $redis_tag=false) {
  $redis_ferm_tag= $redis_tag ? {
    false   => "${environment}_${dcenv}_redis",
    default => "${environment}_${dcenv}_redis_${redis_tag}",
  }
  kbp_ferm::rule { 'Redis access':
    saddr    => $saddr,
    dport    => 6379,
    proto    => 'tcp',
    exported => true,
    ferm_tag => $redis_ferm_tag,
    action   => 'ACCEPT';
  }
}
