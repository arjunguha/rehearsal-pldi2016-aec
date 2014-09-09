class mysql::config {

  require mysql::params
  
  file {"/etc/mysql/my.cnf":
    content => template("mysql/my.cnf.erb"),
    owner => "root",
    group => "root",
    notify => Service["mysql"],
    require => Class["Mysql::Install"],
  }

  # create database user
  mysql::createuser{ $mysql::params::username:
    passwd => $mysql::params::password,
  } ->
  
  # create separate database for this user
  mysql::createdb{ $mysql::params::username:
    owner => $mysql::params::username,
  }
  
}

