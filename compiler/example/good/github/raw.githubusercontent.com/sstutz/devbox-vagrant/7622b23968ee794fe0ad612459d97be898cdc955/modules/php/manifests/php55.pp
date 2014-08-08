class php::php55
{
    exec {
        'add-repo':
            command => 'add-apt-repository ppa:ondrej/php5 -y; apt-get update',
            creates => '/etc/apt/sources.list.d/ondrej-php5-precise.list',
            require => [
                Package['python-software-properties'],
                Exec['remove-5.4-repo']
            ];

           "remove-5.4-repo":
                command => "ppa-purge ppa:ondrej/php5-oldstable",
                onlyif  => "test -f /etc/apt/sources.list.d/ondrej-php5-oldstable-precise.list";
    }


    file {
        '/etc/apt/sources.list.d':
            mode    => '0755',
            ensure  => 'directory';
    }
}


