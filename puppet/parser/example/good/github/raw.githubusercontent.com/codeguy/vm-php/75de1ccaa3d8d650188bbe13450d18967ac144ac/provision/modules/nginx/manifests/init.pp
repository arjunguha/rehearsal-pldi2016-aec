class nginx {
    Class["php"] -> Class["nginx"]

    include nginx::params

    package { "nginx":
        ensure => present
    }

    file { "/etc/nginx/conf.d/php5-fpm.conf":
        ensure => file,
        content => template("nginx/php5-fpm.conf.erb"),
        require => Package["nginx"]
    }

    file { "/etc/nginx/sites-enabled/${nginx::params::domain}":
        ensure => file,
        content => template("nginx/site.conf.erb"),
        require => Package["nginx"]
    }

    file { "/etc/nginx/nginx.conf":
        ensure => file,
        content => template("nginx/nginx.conf.erb"),
        require => Package["nginx"]
    }

    file { "/etc/nginx/mime.types":
        ensure => file,
        content => template("nginx/mime.types.erb"),
        require => Package["nginx"]
    }

    file { "/var/www/logs":
        ensure => directory
    }

    service { "nginx":
        ensure => running,
        hasrestart => true,
        require => File["/var/www/logs"],
        subscribe => [
            File["/etc/nginx/conf.d/php5-fpm.conf"],
            File["/etc/nginx/sites-enabled/${nginx::params::domain}"]
        ]
    }
}
