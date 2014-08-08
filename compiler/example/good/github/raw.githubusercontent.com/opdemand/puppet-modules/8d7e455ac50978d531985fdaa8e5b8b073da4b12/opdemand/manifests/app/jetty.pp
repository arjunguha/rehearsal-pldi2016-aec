class opdemand::app::jetty {

  # require opdemand common and repo
  require opdemand::common
  require opdemand::app::repository

  # initialize dynamic parameters
  class {"jetty::params":
    username => hiera("application/username", "ubuntu"),
    group => hiera("application/group", "ubuntu"),
    home => hiera("application/home", "/home/ubuntu"),
    repository_path => hiera("application/repository_path", "/home/ubuntu/repo"),
    app_name => hiera("application/name", "jetty"),
    port => hiera("application/port", 8000),
  }

  # include relevant jetty classes
  include jetty::install
  include jetty::config
  include jetty::service
  include jetty::deps

}
