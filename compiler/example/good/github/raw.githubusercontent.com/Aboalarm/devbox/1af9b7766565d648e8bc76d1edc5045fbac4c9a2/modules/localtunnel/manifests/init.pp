class localtunnel {
    package { 'localtunnel':
        ensure => installed,
        provider => gem,
    }
}
