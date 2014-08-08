class mongodb::config {

  require mongodb::params
  
  # upstart conf file
  file { "/etc/init/mongodb.conf":
    content => template("mongodb/upstart.conf.erb"),
    mode => "0644",
    notify => Service["mongodb"],
  }
  
  # mongodb conf file
  file { "/etc/mongodb.conf":
    content => template("mongodb/mongodb.conf.erb"),
    mode => "0644",
    notify => Service["mongodb"],
  }
    
}
