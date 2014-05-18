class opdemand::app::custom {

  # require opdemand common and repo
  require opdemand::common
  require opdemand::app::repository
  
  # initialize dynamic parameters
  class {"custom::params":
    username => hiera("application/username", "ubuntu"),
    group => hiera("application/group", "ubuntu"),
    home => hiera("application/home", "/home/ubuntu"),
    repository_path => hiera("application/repository_path", "/home/ubuntu/repo"),
    app_name => hiera("application/name", "custom"),
  }

  # include relevant classes
  include custom::install
  include custom::config
  include custom::service
  include custom::deps

}
