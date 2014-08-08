class vim inherits vim::params {

    package {
        $pkg_name:
            ensure => 'latest',
            require=> Exec['update-apt']
    }

    file {
        '/home/vagrant/.vim':
            ensure  => 'directory',
            mode    => '0755',
            owner   => 'vagrant',
            group   => 'vagrant';

        '/home/vagrant/.vim/colors':
            ensure  => 'directory',
            mode    => '0755',
            owner   => 'vagrant',
            group   => 'vagrant',
            require => File['/home/vagrant/.vim'];

        '/home/vagrant/.vim/colors/wombat256mod.vim':
            owner   => 'vagrant',
            group   => 'vagrant',
            source  => 'puppet:///modules/vim/wombat256mod.vim';
    }
}