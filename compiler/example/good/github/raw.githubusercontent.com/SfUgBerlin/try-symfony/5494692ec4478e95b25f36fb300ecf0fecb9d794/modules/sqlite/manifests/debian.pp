class sqlite::debian {

    include sqlite::params
    
    package { "sqlite":
        name   => $sqlite::params::pkg,
        ensure => installed,
        require => Class['php'],
    }
}