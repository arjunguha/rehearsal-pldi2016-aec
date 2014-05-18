class opdemand::framework::clojure::lein{

  # require opdemand common and repo
  require opdemand::common
  require opdemand::repo::app

  # initialize dynamic parameters
  class {"clojure::params":
    # admin
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
  include clojure::install
  include clojure::config
  include clojure::service
}
