
class opdemand::database::postgresql {
  
  # require opdemand common
  require opdemand::common
  
  # parameterized inputs default to hiera then second arg
  # initialize dynamic parameters
  class {"postgres::params":
    bind => hiera("database/listen", "*"),
    port => hiera("database/port", 5432),
    allow_cidr => hiera("database/allow_cidr", "0.0.0.0/0"),
    username => hiera("database/username", "pguser"),
    password => hiera("database/password", "changeme123"),
  }

  # install and configure postgres
  include postgres::install
  include postgres::config
  include postgres::service

  # # output dynamic orchestration values
  # opdemand::output {"database/host": 
     # key => "database/host",
     # value => $ec2_public_hostname,
  # }
  
}
