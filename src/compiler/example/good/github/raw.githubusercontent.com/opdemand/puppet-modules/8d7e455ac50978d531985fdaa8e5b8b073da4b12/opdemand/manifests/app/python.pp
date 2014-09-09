class opdemand::app::python {

  # require opdemand common and repo
  require opdemand::common
  require opdemand::app::repository

  # initialize dynamic parameters
  class {"python::params":
    username => hiera("application/username", "ubuntu"),
    group => hiera("application/group", "ubuntu"),
    home => hiera("application/home", "/home/ubuntu"),
    repository_path => hiera("application/repository_path", "/home/ubuntu/repo"),
    app_name => hiera("application/name", "python"),
    num_listeners => hiera("application/listeners", 1),
    port => hiera("application/port", 8000),
  }

  # include relevant python classes
  include python::install
  include python::config
  include python::service
  include python::deps

}
