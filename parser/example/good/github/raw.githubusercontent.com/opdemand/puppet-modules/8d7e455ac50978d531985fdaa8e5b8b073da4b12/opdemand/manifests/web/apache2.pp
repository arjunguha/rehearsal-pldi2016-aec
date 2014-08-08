class opdemand::web::apache2 {

  # require opdemand common and repo
  require opdemand::common

  # initialize dynamic parameters
  class {"apache2::params":
    mpm => hiera("apache2/mpm", "prefork"),
  }

  # include relevant classes
  include apache2::install
  include apache2::config
  include apache2::service

}
