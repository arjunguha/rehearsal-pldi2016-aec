class redis {
    # Install redis
    package { 'redis-server':
        ensure => latest,
        require => Exec['apt-get update']
    }

    # Enable the redis service
    service { "redis-server":
        enable => true,
        ensure => running,
        require => Package["redis-server"]
    }
}