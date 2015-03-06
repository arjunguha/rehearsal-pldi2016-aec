class postgresql 
{
    exec { 'psql_add_repo':
        command => '/usr/bin/add-apt-repository ppa:chris-lea/postgresql-9.3'
    }

    exec { 'psql_update_repo':
        command => '/usr/bin/apt-get update',
        require => Exec['psql_add_repo']
    }

    package 
    { 
        "postgresql-9.3":
            ensure  => present,
            require => Exec['psql_update_repo']
    }

    package
    {
        "postgresql-client":
        ensure  => present
    }

    service 
    { 
        "postgresql":
            enable => false,
            ensure => stopped,
            require => Package["postgresql-9.3"]
    }
}