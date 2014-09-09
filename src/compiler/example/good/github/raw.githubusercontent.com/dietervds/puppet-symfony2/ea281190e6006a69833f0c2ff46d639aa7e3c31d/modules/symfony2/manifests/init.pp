# Class: symfony2
#
# This module manages symfony2
#
# Parameters:
#
# Actions:
#
# Requires:
#
# Sample Usage:
#
# [Remember: No empty lines between comments and class definition]
class symfony2 ($mysqlPassword = "dev", $pathToHostfile = "/vagrant/manifests/default") {

    # We base ourselves on a LAMP (with some extras already included, like phpunit, apc, phpmyadmin)
	class {'lamp':
          mysqlPassword => "dev",
          pathToHostfile => "/vagrant/puppet/manifests/default",
    }

    # Then we add the Symfony2 requirements that we haven't met yet

    # SQLite
    package { "php5-sqlite":
         name => "php5-sqlite",
         ensure => present,
         notify  => Service["apache2"],
    }

    # date.timezone setting
    $phpini = '/etc/php5/apache2/php.ini'
    exec { "date.timezone":
            command => "/bin/sed -i 's/^;date.timezone =.*/date.timezone = UTC/' $phpini",
            notify  => Service["apache2"],
    }

    # Intl extension
    package { "php5-intl":
         ensure => present,
    }

    # Set short_open_tags to off
    exec { "short_open_tags":
        command => "/bin/sed -i 's/^short_open_tag = On/short_open_tag = Off/' $phpini",
        notify  => Service["apache2"],
    }
}