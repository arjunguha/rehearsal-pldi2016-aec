class beanstalkd {

    exec { 'add_beanstalkd_repo':
        command => '/usr/bin/add-apt-repository ppa:ivanj/beanstalkd'
    }

    exec { 'update_beanstalkd_repo':
        command => '/usr/bin/apt-get update',
        require => Exec['add_beanstalkd_repo']
    }


    package { 'beanstalkd':
        ensure => latest,
        require => Exec['update_beanstalkd_repo']
    }

    service { 'beanstalkd':
        enable => 'true',
        ensure => 'running',
        hasstatus => 'true',
        restart => '/etc/init.d/beanstalkd restart',
        require   => [
            File['/etc/init/beanstalkd.conf'],
            File['/etc/default/beanstalkd'],
        ],
    }

    file { '/etc/default/beanstalkd':
        owner => 'root',
        group => 'root',
        mode  => '644', 
        ensure => 'present',
        require => Package['beanstalkd'],
        source => 'puppet:///modules/beanstalkd/beanstalkd'
    } 

    file { '/etc/init/beanstalkd.conf':
        owner => 'root',
        group => 'root',
        mode  => '644',
        ensure => 'present',
        require => Package['beanstalkd'],
        source => 'puppet:///modules/beanstalkd/beanstalkd.conf'
    }
}