class php::pear {

    # update PEAR channel
    exec { 'pear-update-channel':
        command => '/usr/bin/pear channel-update pear.php.net',
        require => Package['php-pear']
    }
    
    # upgrade PEAR
    exec { 'pear-upgrade':
        command => '/usr/bin/pear upgrade-all',
        require => Exec['pear-update-channel']
    }

    # install PHPUnit
    exec { 'pear-config-set':
        command => '/usr/bin/pear config-set auto_discover 1',
        require => Exec['pear-upgrade']
    }

    # discover channels
    exec { 'pear-channel-discover-pear-phpunit-de':
        command => '/usr/bin/pear channel-discover pear.phpunit.de; true',
        require => Exec['pear-config-set']
    }

    exec { 'pear-channel-discover-pear-symfony-project-com':
        command => '/usr/bin/pear channel-discover pear.symfony-project.com; true',
        require => Exec['pear-config-set']
    }

    exec { 'pear-channel-discover-components-ez-no':
        command => '/usr/bin/pear channel-discover components.ez.no; true',
        require => Exec['pear-config-set']
    }

    # clear cache before install phpunit
    exec { 'pear-clear-cache':
        command => '/usr/bin/pear clear-cache',
        require => [Exec['pear-channel-discover-pear-phpunit-de'], Exec['pear-channel-discover-pear-symfony-project-com'], Exec['pear-channel-discover-components-ez-no']]
    }

    # install phpunit
    exec { 'pear-install':
        command => '/usr/bin/pear install -a -f phpunit/PHPUnit',
        require => Exec['pear-clear-cache'],
        timeout => 0,
        tries => 10
    }
}