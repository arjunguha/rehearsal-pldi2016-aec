class master {
    include base_packages
    include puppet_support

    user { 'tom':
        shell      => '/bin/zsh',
        managehome => true,
    }

    class { 'sudo': }
    sudo::conf { 'tom':
        priority => 10,
        content  => 'tom ALL=(ALL) ALL
tom ALL=(root) NOPASSWD: /usr/bin/apt-get upgrade
',
    }

}

node /server.*/ {
    include debian
    include firewall
    include ssh
    include httpd
    include bind
    include backups
    include logging

    $packages = [
        'mutt',
        'lynx',
        'vlock',
        'monkeysphere',
        'logwatch',
        'apticron',
        'debian-goodies'
    ]

    package { $packages:
        ensure => installed
    }

    sudo::conf { 'set_secure_path':
        priority => 5,
        content  => 'Defaults secure_path="/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
'
    }

    include master
}

node ubuntu {
    include ntp
    include cron_apt

    include master

    $packages = [
        'ecryptfs-utils',
        'cryptsetup',
    ]
}


node personal inherits ubuntu {
    include desktop_packages

    $ubuntu_release = 'natty'

    package { 'nautilus-dropbox':
        ensure => present,
    }

}

node devel inherits personal {
    include devel_packages
}

node tom-NC10 inherits devel {}
node tom-MS-7599 inherits devel {
    include paranoia

    file { '/media/backup': ensure => directory }
    mount { 'backup':
        ensure   => 'mounted',
        atboot   => true,
        device   => 'UUID=2a1f1fe0-e221-42dc-bbc3-d8b53dcf57da',
        fstype   => 'ext3',
        name     => '/media/backup',
        options  => 'defaults',
        remounts => false,
        require  => File['/media/backup']
    }

    file { '/media/windows1': ensure => directory }
    mount { 'windows1':
        ensure   => 'mounted',
        atboot   => true,
        device   => 'UUID=E0FE2FC8FE2F95B6',
        fstype   => 'ntfs',
        name     => '/media/windows1',
        remounts => false,
        require  => File['/media/windows1']
    }

    file { '/media/windows2': ensure => directory }
    mount { 'windows2':
        ensure   => 'mounted',
        atboot   => true,
        device   => 'UUID=161B2B582E502AD9',
        fstype   => 'ntfs',
        name     => '/media/windows2',
        remounts => false,
        require  => File['/media/windows2']
    }

}
node lt9076 inherits devel {}
