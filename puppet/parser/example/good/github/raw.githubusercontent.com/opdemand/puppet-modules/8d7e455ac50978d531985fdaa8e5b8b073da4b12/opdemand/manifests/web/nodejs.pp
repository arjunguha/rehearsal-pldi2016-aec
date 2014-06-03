class opdemand::web::nodejs {

  # require opdemand common and repo
  require opdemand::common
  require opdemand::repo::app

  # install ppa with precompiled node
  class {"apt":} ->
  apt::ppa {"ppa:chris-lea/node.js":} ->

  # initialize dynamic parameters
  class {"nodejs::params":
    username => hiera("application/username", "ubuntu"),
    home => hiera("application/home", "/home/ubuntu"),
    main => hiera("application/main", "/home/ubuntu/repo/server.js"),
  }

  # include relevant nodejs classes
  include nodejs::install
  include nodejs::config
  include nodejs::service

}
