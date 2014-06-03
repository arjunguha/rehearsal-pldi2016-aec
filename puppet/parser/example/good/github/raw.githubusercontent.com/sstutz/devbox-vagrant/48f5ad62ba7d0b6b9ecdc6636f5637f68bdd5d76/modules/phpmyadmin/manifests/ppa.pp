class phpmyadmin::ppa {
    exec {
        'add-pma-repo':
            command => 'add-apt-repository ppa:nijel/phpmyadmin -y; apt-get update',
            creates => '/etc/apt/sources.list.d/nijel-phpmyadmin-precise.list',
            require => Package['python-software-properties'],
    }
}