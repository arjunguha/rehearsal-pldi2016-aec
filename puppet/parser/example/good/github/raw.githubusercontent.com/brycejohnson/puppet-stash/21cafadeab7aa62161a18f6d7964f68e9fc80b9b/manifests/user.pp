class stash::user{

  exec {"mkdirp-$stash::params::user_home":
    command => "/bin/mkdir -p ${$stash::params::user_home}",
    creates => "${stash::params::user_home}",
  }

  file {"$stash::params::user_home":
    ensure  => directory,
    group   => "$stash::params::group",
    owner   => "$stash::params::user",
    mode    => 0755,
    require => [ Exec["mkdirp-$stash::params::user_home"], User["$stash::params::user"]],
  }

  group { "$stash::params::group":
    name    => "$stash::params::group",
    ensure  => present,
    gid     => "$stash::params::gid",
  }

  user { "$stash::params::user":
    name        => "$stash::params::user",
    ensure      => present,
    home        => "$stash::params::user_home",
    managehome  => true,
    password    => "$stash::params::user_password",
    gid         => "$stash::params::gid",
    comment     => "Stash Servcie User",
    uid         => "$stash::params::uid",
    require     => Group["$stash::params::group"],
  }
}