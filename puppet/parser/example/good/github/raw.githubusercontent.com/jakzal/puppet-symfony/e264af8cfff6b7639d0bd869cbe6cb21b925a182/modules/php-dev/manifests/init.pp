class php-dev::install {
    package { 'php5-xdebug':
        ensure => installed,
        require => Class['php-cli']
    }
    package { 'php5-gd':
        ensure => installed,
        require => Class['php-cli']
    }
    exec { 'pear-auto-discover':
        path => '/usr/bin:/usr/sbin:/bin',
        onlyif => 'test "`pear config-get auto_discover`" = "0"',
        command => 'pear config-set auto_discover 1 system',
        require => Class['php-cli']
    }
    exec { 'pear-update':
        path => '/usr/bin:/usr/sbin:/bin',
        command => 'pear update-channels && pear upgrade-all',
        require => Class['php-cli']
    }
    exec { 'install-phpunit':
        unless => "/usr/bin/which phpunit",
        command => '/usr/bin/pear install pear.phpunit.de/PHPUnit --alldeps',
        require => [Class['php-cli'], Exec['pear-auto-discover'], Exec['pear-update']]
    }
    exec { 'install-phpqatools':
        unless => "/usr/bin/which phpcs",
        command => "/usr/bin/pear install pear.phpqatools.org/phpqatools --alldeps",
        require => [Class['php-cli'], Exec['pear-auto-discover'], Exec['pear-update']]
    }
    exec { 'install-phpdocumentor':
        unless => "/usr/bin/which phpdoc",
        command => "/usr/bin/pear install pear.phpdoc.org/phpDocumentor-alpha --alldeps",
        require => [Class['php-cli'], Exec['pear-auto-discover'], Exec['pear-update']]
    }
}

class php-dev {
    include php-dev::install
}
