class opdemand::database::mysql {

  # require opdemand common
  require opdemand::common

  # parameterized inputs default to hiera then second arg
  # initialize dynamic parameters
  class {"mysql::params":
    bind => hiera("database/bind", "0.0.0.0"),
    port => hiera("database/port", 3306),
    username => hiera("database/username", "mysqluser"),
    password => hiera("database/password", "changeme123"),
  }

  # install and configure mysql
  include mysql::install
  include mysql::config
  include mysql::service

  # # output dynamic orchestration values
  # opdemand::output {"database/host":
     # key => "database/host",
     # value => $ec2_public_hostname,
  # }

}