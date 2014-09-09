
# Base SQL exec
define sqlexec($username, $database, $sql, $sqlcheck) {
  exec{ "sudo -u postgres -i psql -U ${username} -d $database -c \"${sql}\" >> /var/log/puppet/postgresql.sql.log 2>&1 && /bin/sleep 2":
    path        => $path,
    timeout     => 600,
    #user        => "${username}",
    unless      => "sudo -u postgres -i psql -U $username -d $database -c $sqlcheck",
    require =>  [User['postgres'],Service["postgresql"]],
    }
}

# Create a Postgres user
define postgres::createuser($passwd) {
  sqlexec{ createuser:
    username => "postgres",
    database => "postgres",
    # allow createdb
    sql      => "CREATE USER ${name} WITH PASSWORD '${passwd}' CREATEDB;",
    sqlcheck => "\"SELECT usename FROM pg_user WHERE usename = '${name}'\" | grep ${name}",
    require  =>  Service["postgresql"],
  }
}

# Create a Postgres db
define postgres::createdb($owner) {
  sqlexec{ $name:
    username => "postgres",
    database => "postgres",
    sql => "CREATE DATABASE $name WITH OWNER = $owner ;",
    sqlcheck => "\"SELECT datname FROM pg_database WHERE datname ='$name'\" | grep $name",
    require => Service["postgresql"],
  }
}