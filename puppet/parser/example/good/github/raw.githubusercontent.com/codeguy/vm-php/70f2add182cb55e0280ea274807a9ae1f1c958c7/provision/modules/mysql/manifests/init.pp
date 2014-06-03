class mysql {
    Class["base"] -> Class["mysql"]

    include mysql::params

    package { "mysql-server":
        ensure => present
    }

    file { "/etc/mysql/my.cnf":
        ensure => file,
        content => template("mysql/my.cnf.erb"),
        require => Package["mysql-server"]
    }

    # Remove default log files so we can use custom log file size

    exec { "mysql-remove-default-logs":
        command => "rm /var/lib/mysql/ib_logfile*",
        require => Package["mysql-server"],
        unless => "mysql -u root -p${mysql::params::rootPassword}"
    }

    # Start server

    service { "mysql":
        ensure => running,
        require => Exec["mysql-remove-default-logs"],
        subscribe => File["/etc/mysql/my.cnf"]
    }

    exec { "mysql_root_password":
        command => "mysqladmin -u root password '${mysql::params::rootPassword}'",
        require => Service["mysql"],
        unless => "mysql -u root -p${mysql::params::rootPassword}"
    }

    exec { "mysql_user":
        command => "echo \"CREATE USER '${mysql::params::user}'@'%' IDENTIFIED BY '${mysql::params::password}';\" | mysql -u root -p${mysql::params::rootPassword}",
        require => Exec["mysql_root_password"],
        unless => "mysql -u ${mysql::params::user} -p${mysql::params::password}"
    }

    exec { "mysql_database":
        command => "echo \"CREATE DATABASE ${mysql::params::database}; GRANT ALL ON ${mysql::params::database}.* TO '${mysql::params::user}'@'%';\" | mysql -u root -p${mysql::params::rootPassword}",
        require => Exec["mysql_user"],
        unless => "mysql -u ${mysql::params::user} -p${mysql::params::password} ${mysql::params::database}"
    }
}
