class opdemand::cache::memcache {

  require opdemand::common

  # initialize dynamic parameters
  class {"memcache::params":
    bind => hiera("cache/bind", "0.0.0.0"),
    port => hiera("cache/port", "11211"),
    username => hiera("cache/username", "memcache"),
    size => hiera("cache/size", "256"),
  }
  
  # include relevant classes
  include memcache::install
  include memcache::config
  include memcache::service
  
}