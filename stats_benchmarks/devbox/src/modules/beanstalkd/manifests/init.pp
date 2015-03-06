class beanstalkd {

    package { 'beanstalkd':
        ensure => latest,
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