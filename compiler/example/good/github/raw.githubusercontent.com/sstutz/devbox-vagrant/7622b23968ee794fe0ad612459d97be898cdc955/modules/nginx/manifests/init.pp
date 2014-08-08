class nginx(
) inherits nginx::params {

    exec {
        "remove-apache2-startup":
            command => "update-rc.d -f apache2 remove",
            notify  => Exec['kill-apache2'],
            onlyif  => "test -f /etc/rc2.d/*apache*";

        "kill-apache2":
            command     => "killall -9 apache2; test -d /;",
            refreshonly => true,
            notify      => Service[$svc_name];

        "disable-sendfile":
            command => "sed -i 's~sendfile on~sendfile off~g' /etc/nginx/nginx.conf",
            require => Package[$svc_name],
            unless  => 'grep -R "sendfile off;" "/etc/nginx/nginx.conf"',
            notify  => Service[$svc_name];
    }


    package {
        $pkg_name:
            ensure => latest,
            require=> Exec['update-apt'];

        $extensions:
            ensure => latest,
            require=> Package[$pkg_name]
    }


    service {
        $svc_name:
            ensure  => running,
            enable  => true,
            require => Package[$pkg_name]
    }

    file {
        "/etc/nginx/sites-available/default":
            mode    => '0644',
            ensure  => present,
            require => Package["nginx"],
            source  => "puppet:///modules/nginx/default";

        "/etc/nginx/sites-enabled/default":
            mode    => '0644',
            ensure  => link,
            target  => "/etc/nginx/sites-available/default",
            require => File["/etc/nginx/sites-available/default"],
            notify  => Service["nginx"];

        "/etc/nginx/conf.d/global/":
            mode    => '0644',
            ensure  => "directory",
            require => Package["nginx"],
            notify  => Service[$svc_name],
            source  => "puppet:///modules/nginx/global/";

        "/etc/nginx/conf.d/global/00-cachecontrol.conf":
            mode    => '0644',
            ensure  => present,
            require => File["/etc/nginx/conf.d/global/"],
            notify  => Service[$svc_name],
            source  => "puppet:///modules/nginx/global/00-cachecontrol.conf";

        "/etc/nginx/conf.d/global/10-php-fpm.conf":
            mode    => '0644',
            ensure  => present,
            require => File["/etc/nginx/conf.d/global/"],
            notify  => Service[$svc_name],
            source  => "puppet:///modules/nginx/global/10-php-fpm.conf";

        "/etc/nginx/conf.d/global/20-deny-access.conf":
            mode    => '0644',
            ensure  => present,
            require => File["/etc/nginx/conf.d/global/"],
            notify  => Service[$svc_name],
            source  => "puppet:///modules/nginx/global/20-deny-access.conf";

    }
}
