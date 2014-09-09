class postfix {
    # Install postfix
    package { 'postfix':
        ensure => 'latest',
        require => Exec['apt-get update']
    }

    # Enable the postfix service
    service { 'postfix':
        ensure => running,
        enable => true,
        require => Package['postfix'],
    }
}