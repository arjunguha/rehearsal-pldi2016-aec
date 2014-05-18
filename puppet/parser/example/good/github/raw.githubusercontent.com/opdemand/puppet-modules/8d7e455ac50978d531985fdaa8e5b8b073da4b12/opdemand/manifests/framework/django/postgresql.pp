class opdemand::framework::django::postgresql {

  # require opdemand common and repo
  require opdemand::common
  require opdemand::repo::app
  
  # initialize dynamic parameters
  class {"django::params":
    # admin
    admin_name => hiera("admin/name", "Administrator"),
    admin_username => hiera("admin/username", "admin"),
    admin_password => hiera("admin/password", "changeme123"),
    admin_email => hiera("admin/email", "admin@example.org"),
    # database
    database_type => hiera("database/type", "postgresql"),
    # service 
    bind => hiera("application/bind", "0.0.0.0"),
    port => hiera("application/port", "8080"),
    # daemon/repository
    username => hiera("application/username", "ubuntu"),
    group => hiera("application/group", "ubuntu"),
    home => hiera("application/home", "/home/ubuntu"),
    repository_path => hiera("application/repository_path", "/home/ubuntu/repo"),
  }

  # include relevant classes
  include django::install
  include django::config
  include django::service

}
