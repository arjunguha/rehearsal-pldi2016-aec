class opdemand::cache::redis {

  require opdemand::common

  # initialize dynamic parameters
  class {"redis::params":
    bind => hiera("cache/bind", "0.0.0.0"),
    port => hiera("cache/port", "6379"),
  }
  
  # include relevant classes
  include redis::install
  include redis::config
  include redis::service
  
}