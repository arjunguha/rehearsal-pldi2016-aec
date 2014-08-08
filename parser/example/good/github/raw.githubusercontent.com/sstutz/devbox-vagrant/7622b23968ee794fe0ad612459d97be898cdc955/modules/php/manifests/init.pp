class php(
    $version = '5.3',
    $webserver='nginx',
    $xdebug  = true,
    $tools = true,
) inherits php::params {

    Class['php']->Class[$webserver]

    if ($version == '5.3') {
        exec {
           "remove-5.4-repo":
                command => "ppa-purge ppa:ondrej/php5-oldstable",
                onlyif  => "test -f /etc/apt/sources.list.d/ondrej-php5-oldstable-precise.list";

            "remove-5.5-repo":
                command => "ppa-purge ppa:ondrej/php5",
                onlyif  => "test -f /etc/apt/sources.list.d/ondrej-php5-precise.list";
        }
        # purge php5.4 and php55 repositories,
        # update the repos, and install the rest
    }

    if ($version == '5.4') {
        include php::php54
        Class['php::php54']->Class['php']
    }

    if ($version == '5.5') {
        include php::php55
        Class['php::php55']->Class['php']
    }

    if ($tools == true) {
        include php::tools
        Class['php']->Class['php::tools']
    }

    $cfg_path = $version ? {
        '5.3' => '/usr/lib/php5/20090626+lfs',
        '5.4' => '/usr/lib/php5/20100525+lfs',
        '5.5' => '/usr/lib/php5/20121212',
    }

    package {
        $pkg_name:
            ensure  => "latest",
            require => [
                Exec['update-apt'],
                Package['build-essential']
            ];

        $svc_name:
            require => Package[$pkg_name];

        $php_exts:
            ensure => "latest",
            require => Package[$svc_name];
    }

    service {
        $svc_name:
            enable => true,
            ensure => running,
            require=> Package[$pkg_name],
    }

    exec {
        "fpm-socket":
            command => "sed -i 's~listen = 127.0.0.1:9000~listen = /var/run/php5-fpm.sock~g' /etc/php5/fpm/pool.d/www.conf",
            require => Package[$svc_name],
            unless  => 'grep -R "listen = /var/run/php5-fpm.sock" "/etc/php5/fpm/pool.d/www.conf"',
            notify  => Service[$svc_name];


        "set-display-error":
            cwd => "/etc/php5/fpm/",
            command => "sed -i 's~^display_errors = Off~display_errors = On~g' php.ini",
            unless => 'grep -R "display_errors = On" "php.ini"',
            require => Package[$svc_name],
            notify  => Service[$svc_name];


        "set-error-reporting":
            cwd => "/etc/php5/fpm/",
            command => "sed -i 's~^error_reporting = .*~error_reporting = -1~g' php.ini",
            unless => 'grep -R "error_reporting = -1" "php.ini"',
            require => Package[$svc_name],
            notify  => Service[$svc_name];


        "set-startup-errors":
            cwd => "/etc/php5/fpm/",
            command => "sed -i 's~^display_startup_errors = Off~display_startup_errors = On~g' php.ini",
            unless => 'grep -R "display_startup_errors = On" "php.ini"',
            require => Package[$svc_name],
            notify  => Service[$svc_name];


        "set-post-max-size":
            cwd => "/etc/php5/fpm/",
            command => "sed -i 's~^post_max_size = .*~post_max_size = 50M~g' php.ini",
            unless => 'grep -R "post_max_size = 50M" "php.ini"',
            require => Package[$svc_name],
            notify  => Service[$svc_name];


        "set-upload-max-filesize":
            cwd => "/etc/php5/fpm/",
            command => "sed -i 's~^upload_max_filesize = .*~upload_max_filesize = 50M~g' php.ini",
            unless => 'grep -R "upload_max_filesize = 50M" "php.ini"',
            require => Package[$svc_name],
            notify  => Service[$svc_name];
    }

    if ($xdebug == true) {
        $cwd_path = $version ? {
            '5.3' => '/etc/php5/conf.d',
            '5.4' => '/etc/php5/conf.d',
            '5.5' => '/etc/php5/mods-available',
        }

        exec {
            'install-xdebug':
                command => 'aptitude install php5-xdebug',
                creates => "$cfg_path/xdebug.so",
                require => Package['php-pear', 'php5-dev'];

            'prepand-extension':
                cwd         => "$cwd_path",
                command     => "sed -i '1i zend_extension=$cfg_path/xdebug.so\n' xdebug.ini",
                notify      => Service[$webserver],
                refreshonly =>true;
        }

        file {
            "$cwd_path/xdebug.ini":
                replace => "no",
                require => Exec['install-xdebug'],
                notify  => Exec['prepand-extension'],
                source  => 'puppet:///modules/php/xdebug.ini';
        }
    }
}