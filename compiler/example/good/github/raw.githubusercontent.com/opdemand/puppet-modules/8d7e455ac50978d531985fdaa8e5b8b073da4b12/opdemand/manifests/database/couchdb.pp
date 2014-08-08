class opdemand::database::couchdb {

  require opdemand::common

  # initialize dynamic parameters
  class {"couchdb::params":
    allow_cidr => hiera("database/allow_cidr", "0.0.0.0/0"),
    bind => hiera("database/bind", "0.0.0.0"),
    port => hiera("database/port", "5984"),
  }
  
  # include relevant classes
  include couchdb::install
  include couchdb::config
  include couchdb::service
  
}