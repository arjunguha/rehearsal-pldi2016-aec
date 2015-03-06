class php {

    Exec { path => [ "/bin/", "/sbin/" , "/usr/bin/", "/usr/sbin/" ] }

    exec { 'update_repo':
        command => '/usr/bin/apt-get update',
    }
    
    $packages = ['php5', 'php5-mcrypt', 'php-xml-parser', 'php5-mysql', 'php5-cli', 'php5-curl', 'php5-fpm', 'libssh2-1-dev', 'php5-common', 'php-pear', 'php5-gd', 'php5-imagick', 'php5-xdebug']

    package { $packages:
        ensure => latest,
        require => Exec['update_repo']
    }

    file { 'php.ini':
        path => '/etc/php5/fpm/php.ini',
        ensure => file,
        owner => root,
        group => root,
        source => 'puppet:///modules/php/php.ini',
        require => Package['php5-fpm'],
    }
    
    file { 'browscap.ini':
        path => '/etc/php5/browscap.ini',
        ensure => file,
        owner => root,
        group => root,
        source => 'puppet:///modules/php/browscap.ini',
        require => Package['php5-fpm'],
    }

    file {'/etc/php5/conf.d':
        ensure => 'directory',
        require => Package['php5-mcrypt'],
    }

    file { '/etc/php5/conf.d/mcrypt.ini':
        ensure => 'link',
        target => '/etc/php5/mods-available/mcrypt.ini',
        require => File['/etc/php5/conf.d'],
    }

    exec { 'php5enmod_mcrypt':
        command => 'php5enmod mcrypt && service php5-fpm restart',
        require => File['/etc/php5/conf.d/mcrypt.ini'],
    }

    service { 'apache2':
        ensure => stopped,
        enable => false,
    }
}
