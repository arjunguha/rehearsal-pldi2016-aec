class supervisor {
    package { 'supervisor':
        ensure => installed,
    }

    file { 'supervisor.conf':
        path => '/etc/supervisor/supervisord.conf',
        ensure => file,
        owner => root,
        group => root,
        source => 'puppet:///modules/supervisor/supervisord.conf',
        require => Package['supervisor'],
    }
}
