class mysql::settings {
    # The node-level $mysql_package_type gives the "flavor" 
    # of MySQL installed here, and defaults to 'mysql'.  
    # We make a local variable with the default filled in
    $package_type = $mysql_package_type ? {
        "mysql56" => "mysql56",
        "mariadb55" => "mariadb55",
        "percona55" => "percona55",
        "percona51" => "percona51",
        "mysql" => "mysql",
        default => "mysql",
    }
    notice("Using MySQL package type ${package_type}")

    # the packages to install for this package type
    $packages = $package_type ? {
        "mysql56" => ["MySQL-server-5.6.12"],
        "mariadb55" => ["MariaDB-server"],
        "percona55" => ["Percona-Server-server-55"],
        "percona51" => ["Percona-Server-server-51"], # mysql::client gets perl-DBD-MySQL
        "mysql" => ["mysql-server"],
    }

    # the name of the Service instance to notify
    $service_name = $package_type ? {
        "mysql56" => "mysql",
        "mariadb55" => "mysql",
        "percona55" => "mysql",
        "percona51" => "mysql",
        "mysql" => "mysqld",
    }
}
