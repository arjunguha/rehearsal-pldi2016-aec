class apc::debian {

    include apc::params
    
    package { "apc":
        name   => $apc::params::pkg,
        ensure => installed,
        require => Class['php'],
    }
    
    augeas{ "apc.ini settings":
        context => "/files/${apc::params::conf}/apc.ini/.anon/",
        lens => "PHP.lns",
        incl => "${apc::params::conf}/apc.ini",
        changes => [
            "set enabled 1",
            "set shm_size ${apc::params::shmsize}",
            "set shm_segments ${apc::params::shmsegments}",
            "set ttl ${apc::params::ttl}"
        ],
        require => [ 
            Package["apc"],
            Class["augeas"],
        ],
    }  
}