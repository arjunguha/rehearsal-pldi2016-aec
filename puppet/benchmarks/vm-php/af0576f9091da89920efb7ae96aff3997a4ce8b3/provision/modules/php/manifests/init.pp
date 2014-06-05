class php {
    Class["memcache"] -> Class["php"]

    include nginx::params
    include mysql::params

    # Install PHP

    package { "php":
        name => [
            "php-pear",
            "php5-cgi",
            "php5-cli",
            "php5-common",
            "php5-curl",
            "php5-dbg",
            "php5-dev",
            "php5-fpm",
            "php5-gd",
            "php5-intl",
            "php5-json",
            "php5-mcrypt",
            "php5-memcached",
            "php5-mysqlnd",
            "php5-sqlite",
            "php5-tidy",
            "php5-xdebug"
        ],
        ensure => installed
    }

    # Configure PHP

    file { "/etc/php5/fpm/php-fpm.conf":
        ensure => file,
        content => template("php/php-fpm.conf.erb"),
        require => Package["php"]
    }

    file { "/etc/php5/fpm/php.ini":
        ensure => file,
        content => template("php/php.ini.erb"),
        require => Package["php"]
    }

    file { "/etc/php5/fpm/pool.d/www.conf":
        ensure => file,
        content => template("php/www.conf.erb"),
        require => Package["php"]
    }

    # Run PHP

    service { "php5-fpm":
        ensure => running,
        hasrestart => true,
        require => Package["php"],
        subscribe => [
            File["/etc/php5/fpm/php-fpm.conf"],
            File["/etc/php5/fpm/php.ini"],
            File["/etc/php5/fpm/pool.d/www.conf"]
        ]
    }

    # Configure xdebug

    file { "/var/www/xdebug":
        ensure => directory,
        require => Package["php"]
    }

    file { "/etc/php5/fpm/conf.d/xdebug-custom.ini":
        ensure => file,
        content => template("php/xdebug.ini"),
        require => Package["php"],
        notify => Service["php5-fpm"]
    }

    # Install xhprof

    exec { "php-xhprof":
        command => "sudo pecl install http://pecl.php.net/get/xhprof-0.9.4.tgz",
        unless => "test -f `php-config --extension-dir`/xhprof.so"
    }

    file { "/etc/php5/fpm/conf.d/xhprof.ini":
        ensure => file,
        content => template("php/xhprof.ini.erb"),
        require => Exec["php-xhprof"],
        notify => Service["php5-fpm"]
    }

    # Install xhprof ui

    exec { "php-xhprof-ui":
        command => "git clone git://github.com/preinheimer/xhprof.git",
        cwd => "/var/www",
        creates => "/var/www/xhprof"
    }

    file { "/var/www/xhprof/xhprof_lib/config.php":
        ensure => file,
        content => template("php/xhprof.config.php.erb"),
        require => Exec["php-xhprof-ui"]
    }

    exec { "xhprof-database":
        command => "echo \"CREATE DATABASE xhprof; GRANT ALL ON xhprof.* TO '${mysql::params::user}'@'localhost'; USE xhprof; SOURCE /var/www/provision/modules/php/templates/xhprof.sql;\" | mysql -u root -p${mysql::params::rootPassword}",
        require => Exec["php-xhprof-ui"],
        unless => "mysql -u ${mysql::params::user} -p${mysql::params::password} xhprof"
    }

    file { "/var/www/xhprof/runs":
        ensure => directory,
        require => Exec["php-xhprof-ui"]
    }
}
