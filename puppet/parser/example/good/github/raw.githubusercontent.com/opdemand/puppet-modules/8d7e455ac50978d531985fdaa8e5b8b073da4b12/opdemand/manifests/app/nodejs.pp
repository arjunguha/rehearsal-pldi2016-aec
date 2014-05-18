class opdemand::app::nodejs {

  # require opdemand common and repo
  require opdemand::common
  require opdemand::app::repository
  
  # initialize dynamic parameters
  class {"nodejs::params":
    username => hiera("application/username", "ubuntu"),
    group => hiera("application/group", "ubuntu"),
    home => hiera("application/home", "/home/ubuntu"),
    repository_path => hiera("application/repository_path", "/home/ubuntu/repo"),
    app_name => hiera("application/name", "nodejs"),
  }

  # include relevant classes
  include nodejs::install
  include nodejs::config
  include nodejs::service
  include nodejs::deps

}
