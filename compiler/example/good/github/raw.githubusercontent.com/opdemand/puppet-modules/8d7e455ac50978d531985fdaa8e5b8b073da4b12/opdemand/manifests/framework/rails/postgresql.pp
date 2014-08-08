class opdemand::framework::rails::postgresql {

  # require opdemand common and repo
  require opdemand::common
  require opdemand::repo::app
  require opdemand::web::nginx
  
  # initialize dynamic parameters
  class {"rails::params":
    # admin
    admin_name => hiera("admin/name", "Administrator"),
    admin_username => hiera("admin/username", "admin"),
    admin_password => hiera("admin/password", "changeme123"),
    admin_email => hiera("admin/email", "admin@example.org"),
    # database
    database_type => hiera("database/type", "postgresql"),
    database_host => hiera("database/host", "localhost"),
    database_port => hiera("database/port", "5432"),
    database_name => hiera("database/name", "rails"),
    database_username => hiera("database/username", "rails"),
    database_password => hiera("database/password", "changeme123."),
    # service
    bind => hiera("application/bind", "0.0.0.0"),
    port => hiera("application/port", "8080"),
    # daemon/repository
    username => hiera("application/username", "ubuntu"),
    group => hiera("application/group", "ubuntu"),
    home => hiera("application/home", "/home/ubuntu"),
    repository_path => hiera("application/repository_path", "/home/ubuntu/repo"),
    mode => hiera("application/mode", "production"),
  }
  
  # include relevant classes
  include rails::install
  include rails::config
  include rails::service
  include nginx
  include rails::nginx

}
