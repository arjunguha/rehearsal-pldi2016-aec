class xhprof {
    # Install xhprof. PECL version doesn't run with PHP 5.4, so we have
    # to compile and install manually.
    exec { "xhprof.download":
        command => "git clone --depth 1 git://github.com/preinheimer/xhprof.git",
        cwd => "/var/www",
        creates => "/var/www/xhprof",
        unless => "ls /var/www/xhprof",
        require => [Package['apache2'], Package['git']],
    }
    exec { "xhprof.phpize":
        command => "phpize",
        cwd => "/var/www/xhprof/extension",
        unless => "php -m | grep xhprof",
        require => [Package['php5-dev'], Exec["xhprof.download"]]
    }
    exec { "xhprof.configure":
        command => "sh ./configure",
        cwd => "/var/www/xhprof/extension",
        unless => "php -m | grep xhprof",
        require => Exec["xhprof.phpize"]
    }
    exec { "xhprof.make":
        command => "make",
        cwd => "/var/www/xhprof/extension",
        unless => "php -m | grep xhprof",
        require => [Package['make'], Exec["xhprof.configure"]]
    }
    exec { "xhprof.make.install":
        command => "make install",
        cwd => "/var/www/xhprof/extension",
        creates => "/usr/lib/php5/20100525/xhprof.so",
        unless => "php -m | grep xhprof",
        require => [Package['make'], Exec["xhprof.make"]]
    }
    file { "/etc/php5/conf.d/xhprof.ini":
        content => "extension=xhprof.so",
        require => Exec["xhprof.make.install"],
        notify => Service['apache2']
    }

    # Setup xhprof web UI
    file { "/var/www/xhprof/xhprof_lib/config.php":
        ensure => file,
        source => "puppet:///modules/xhprof/config.php",
        replace => false,
        require => Exec["xhprof.download"]
    }
    exec { "xhprof.web.database":
        command => 'mysql -uroot -proot -e "create database xhprof; use xhprof; CREATE TABLE \`details\` (\`id\` char(17) NOT NULL, \`url\` varchar(255) default NULL, \`c_url\` varchar(255) default NULL, \`timestamp\` timestamp NOT NULL default CURRENT_TIMESTAMP on update CURRENT_TIMESTAMP, \`server name\` varchar(64) default NULL, \`perfdata\` MEDIUMBLOB, \`type\` tinyint(4) default NULL, \`cookie\` BLOB, \`post\` BLOB, \`get\` BLOB, \`pmu\` int(11) unsigned default NULL, \`wt\` int(11) unsigned default NULL, \`cpu\` int(11) unsigned default NULL, \`server_id\` char(3) NOT NULL default \'t11\', \`aggregateCalls_include\` varchar(255) DEFAULT NULL, PRIMARY KEY  (\`id\`), KEY \`url\` (\`url\`), KEY \`c_url\` (\`c_url\`), KEY \`cpu\` (\`cpu\`), KEY \`wt\` (\`wt\`), KEY \`pmu\` (\`pmu\`), KEY \`timestamp\` (\`timestamp\`)) ENGINE=MyISAM DEFAULT CHARSET=utf8;"',
        unless => 'mysql -uroot -proot xhprof -e "exit"',
        require => Exec['set-mysql-password']
    }
    file { "/var/www/xhprof/index.php":
        content => "<?php header('Location: /xhprof/xhprof_html/');",
        require => Exec["xhprof.download"]
    }
    file { "/var/www/xhprof/.htaccess":
        content => "php_value error_reporting 30719",
        require => Exec["xhprof.download"]
    }
}