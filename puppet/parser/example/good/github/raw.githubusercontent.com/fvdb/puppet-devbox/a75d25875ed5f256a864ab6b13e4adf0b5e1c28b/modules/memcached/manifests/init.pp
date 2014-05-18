class memcached {
    # Install memcached
    package { 'memcached':
        ensure => latest,
        require => Exec['apt-get update']
    }

    # Enable the redis service
    service { "memcached":
        enable => true,
        ensure => running,
        require => Package["memcached"]
    }
}