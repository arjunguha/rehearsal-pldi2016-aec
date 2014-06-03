class mysql::createdb {
    exec { "create-ezp-db":
      command => "/usr/bin/mysql -uroot -e \"create database $database_name character set utf8; grant all on $database_name.* to $database_user@localhost identified by '$database_password';\"",
      require => Service["mysqld"],
      returns => [ 0, 1, '', ' ']
    }
}