class base {
    exec { "apt-update":
        command => "sudo apt-get update"
    }

    package { "essential-packages":
        name => [
            "sudo",
            "aptitude",
            "build-essential",
            "wget",
            "unzip",
            "git",
            "strace",
            "libmcrypt-dev",
            "python-software-properties"
        ],
        ensure => installed,
        require => Exec["apt-update"]
    }

    exec { "ppa-ondrej-php5":
        command => "sudo add-apt-repository ppa:ondrej/php5",
        creates => "/etc/apt/sources.list.d/ondrej-php5-precise.list",
        require => Package["essential-packages"]
    }

    exec { "apt-update-again":
        command => "sudo apt-get update",
        require => Exec["ppa-ondrej-php5"],
        unless => "test -f /usr/bin/php"
    }
}
