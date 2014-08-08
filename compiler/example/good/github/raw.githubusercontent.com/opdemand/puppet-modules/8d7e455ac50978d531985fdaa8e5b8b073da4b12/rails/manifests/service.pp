class rails::service {

  require rails::params

  service {"rails":
    ensure => running,
    name => "rails",
    provider => upstart,
    require => [ Class[Rails::Install], Class[Rails::Config] ],
    subscribe => Vcsrepo["$rails::params::repository_path"],
  } ->

  rails::dbcreate {"rails":} ->
  rails::dbsync {"rails":}

}
