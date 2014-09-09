class mysql {
    # Install mysql
    package { "mysql-server":
        ensure => latest,
        require => Exec['apt-get update']
    }

    # Enable the MySQL service
    service { "mysql":
        enable => true,
        ensure => running,
        require => Package["mysql-server"],
    }

    # Set MySQL password to "root"
    exec { "set-mysql-password":
        unless => "mysqladmin -uroot -proot status",
        command => "mysqladmin -uroot password root",
        require => Service["mysql"],
    }
}