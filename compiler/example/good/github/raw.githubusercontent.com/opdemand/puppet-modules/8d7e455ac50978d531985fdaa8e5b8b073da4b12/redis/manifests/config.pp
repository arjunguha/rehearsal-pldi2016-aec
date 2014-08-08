class redis::config {
  
  require redis::params
  
  file {"/etc/redis/redis.conf":
    owner => "root",
    group => "root",
    mode => 0644,
    content => template("redis/redis.conf.erb"),
    require => Package["redis-server"],
  }  

}
