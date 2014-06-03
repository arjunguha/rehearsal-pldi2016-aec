define rails::dbcreate {
    exec { "sudo -u $rails::params::username rake db:create:all":
      path => $path,
      user => "$rails::params::username",
      cwd => "$rails::params::repository_path/app",
      require => [Vcsrepo["$rails::params::repository_path"], Package["rake"]],
    }
}

define rails::dbsync {
    exec { "sudo -u $rails::params::username rake db:migrate":
      path => $path,
      user => "$rails::params::username",
      cwd => "$rails::params::repository_path/app",
      require =>  Service["rails"],
      subscribe => Vcsrepo["$rails::params::repository_path"],
    }
}
