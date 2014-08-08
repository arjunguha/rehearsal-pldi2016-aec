class nginx::install {
    package { 'nginx':
        ensure => installed,
        require => Class['php-fpm']
    }
}

class nginx::configure {
}

class nginx::run {
    service { nginx:
        enable => true,
        ensure => running,
        hasstatus => true,
        hasrestart => true,
        require => Class['nginx::install', 'nginx::configure'],
    }
}

define nginx::vhost(
    $server_name = '*.dev',
    $template = 'nginx/dev.erb',
    $site = 'dev',
    $root = '/home/vagrant/$host/web'
) {
    $sitesavailable = '/etc/nginx/sites-available'
    $sitesenabled = '/etc/nginx/sites-enabled'
    file {"$sitesavailable/$site":
        content => template($template),
        owner   => 'root',
        group   => 'root',
        mode    => '755',
        require => Package['nginx'],
        notify  => Service['nginx']
    }
    file { "$sitesenabled/$site":
        ensure => 'link',
        target => "$sitesavailable/$site",
        require => Package['nginx'],
        notify  => Service['nginx']
    }
}

class nginx {
    include nginx::install
    include nginx::configure
    include nginx::run
}
