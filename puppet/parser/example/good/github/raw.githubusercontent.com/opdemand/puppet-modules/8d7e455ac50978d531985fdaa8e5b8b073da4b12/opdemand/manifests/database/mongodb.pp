class opdemand::database::mongodb {

  require opdemand::common

  # initialize dynamic parameters
  class {"mongodb::params":
    port => hiera("database/port", 27017),
  }
  
  # include relevant classes
  include mongodb::install
  include mongodb::config
  include mongodb::service
  
}