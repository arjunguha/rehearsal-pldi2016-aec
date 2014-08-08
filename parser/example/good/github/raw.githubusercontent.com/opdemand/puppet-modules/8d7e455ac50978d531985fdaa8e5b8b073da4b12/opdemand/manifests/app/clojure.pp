class opdemand::app::clojure {

  # require opdemand common and repo
  require opdemand::common
  require opdemand::app::repository
  
  # initialize dynamic parameters
  class {"clojure::params":
    username => hiera("application/username", "ubuntu"),
    group => hiera("application/group", "ubuntu"),
    home => hiera("application/home", "/home/ubuntu"),
    repository_path => hiera("application/repository_path", "/home/ubuntu/repo"),
    app_name => hiera("application/name", "clojure"),
  }

  # include relevant classes
  include clojure::install
  include clojure::config
  include clojure::service
  include clojure::deps

}
