class opdemand::web::nginx {
  
  require opdemand::common

  # initialize dynamic parameters
  class {"nginx::params":
    # nginx params
    template_name => hiera("nginx/template_name", "default"),
    public_root => hiera("nginx/public_root", "/home/ubuntu/repo/public"),
    # application params
    app_name => hiera("application/name", "nginx"),
    start_port => hiera("application/port", "5000"),
    num_listeners => hiera("application/listeners", 1),
  }

  # include relevant classes
  include nginx::install
  include nginx::config
  include nginx::service

}