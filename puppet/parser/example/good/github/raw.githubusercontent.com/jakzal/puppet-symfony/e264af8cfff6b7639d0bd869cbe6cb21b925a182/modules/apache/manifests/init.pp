class apache::install {
    package { 'apache2-mpm-worker':
        ensure => installed,
        require => Class['php-fpm']
    }
    package { 'libapache2-mod-fastcgi':
        ensure => installed,
        require => Class['php-fpm']
    }
}

class apache::configure {
}

class apache::run {
    service { apache2:
        enable => true,
        ensure => running,
        hasstatus => true,
        hasrestart => true,
        require => Class['apache::install', 'apache::configure'],
    }
}

class apache {
    include apache::install
    include apache::configure
    include apache::run
}
