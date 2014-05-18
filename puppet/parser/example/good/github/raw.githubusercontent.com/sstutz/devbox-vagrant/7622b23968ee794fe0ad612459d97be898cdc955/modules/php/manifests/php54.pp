class php::php54
{
    exec {
        'add-repo':
            command => 'add-apt-repository ppa:ondrej/php5-oldstable -y; apt-get update',
            creates => '/etc/apt/sources.list.d/ondrej-php5-oldstable-precise.list',
            require => [
                Package['python-software-properties'],
                Exec['remove-5.5-repo']
            ];

            "remove-5.5-repo":
                command => "ppa-purge ppa:ondrej/php5",
                onlyif  => "test -f /etc/apt/sources.list.d/ondrej-php5-precise.list";
    }


    file {
        '/etc/apt/sources.list.d':
            mode    => '0755',
            ensure  => 'directory';
    }
}


