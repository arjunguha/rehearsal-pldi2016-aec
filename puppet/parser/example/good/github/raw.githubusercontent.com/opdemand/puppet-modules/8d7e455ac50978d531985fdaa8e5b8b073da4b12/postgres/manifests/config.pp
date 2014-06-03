class postgres::config {

  require postgres::params
  
  file {"/etc/postgresql/9.1/main/postgresql.conf":
    content => template("postgres/postgresql.conf.erb"),
    owner => "root",
    group => "root",
    notify => Service["postgresql"],
    require => Package["postgresql"],
  }

  file { "/etc/postgresql/9.1/main/pg_hba.conf":
    content => template("postgres/pg_hba.conf.erb"),  
    owner  => "root",
    group  => "root",
    notify => Service["postgresql"],
    require => Package["postgresql"],
  }
  
  # create database user
  postgres::createuser{ $postgres::params::username:
    passwd => $postgres::params::password,
  } ->
  
  # create separate database for this user
  postgres::createdb{ $postgres::params::username:
    owner => $postgres::params::username,
  }
  
}

