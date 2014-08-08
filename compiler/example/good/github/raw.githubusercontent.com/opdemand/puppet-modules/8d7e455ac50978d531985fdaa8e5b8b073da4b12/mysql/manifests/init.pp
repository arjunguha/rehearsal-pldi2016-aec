
# Base MySQL exec
define sqlexec($username, $database, $sql, $sqlcheck) {
  exec{ "sudo -u mysql mysql -u ${username} -D ${database} -e \"${sql}\" >> /var/log/puppet/mysql.log 2>&1 && /bin/sleep 2":
    path        => $path,
    timeout     => 600,
    user        => "root",
    unless      => "sudo -u mysql mysql -u ${username} -D ${database} -e ${sqlcheck}",
    require =>  Class["Mysql::Service"],
    }
}

# Create a mysql user
define mysql::createuser($passwd, $host = "%") {
  sqlexec{ createuser:
    username => "root",
    database => "mysql",
    sql      => "GRANT ALL PRIVILEGES ON ${name}.* to '${name}'@'${host}' IDENTIFIED BY '${passwd}'; GRANT ALL PRIVILEGES ON ${name}.* to '${name}'@'localhost' IDENTIFIED BY '${passwd}';",
    sqlcheck => "\"SELECT user FROM mysql.user WHERE user='${name}';\" | grep ${name}",
  }
}

# Create a mysql db
define mysql::createdb($owner) {
  sqlexec{ $name:
    username => "root",
    database => "mysql",
    sql => "CREATE DATABASE ${name};",
    sqlcheck => "\"SELECT SCHEMA_NAME FROM INFORMATION_SCHEMA.SCHEMATA WHERE SCHEMA_NAME = '${name}';\" | grep ${name}",
  }
}