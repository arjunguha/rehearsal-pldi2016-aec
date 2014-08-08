class base_packages {
    $base_packages = [
        'ack-grep',
        'curl',
        'dos2unix',

        'duplicity',
        # https://bugs.launchpad.net/ubuntu/+source/duplicity/+bug/959089
        'python-paramiko',

        'git',
        'ghc6',
        'htop',
        'iotop',
        'irssi',
        'jekyll',
        'moreutils',
        'mtr',
        'netcat',
        'netcat6',
        'pv',
        'pwgen',
        'python-gdata',
        'rdiff-backup',
        'screen',
        'strace',
        'tcpdump',
        'tmux',
        'tree',
        'unzip',
        'urlview',
        'wget',
        'whois',
        'zsh',

    ]

    case $::operatingsystem {
        'Debian': { $os_packages = [
          'apt-file', 'molly-guard', 'vim-puppet', 'vim-addon-manager', 'vim-scripts', 'aptitude',
          'dnsutils', 'gnupg', 'vim', 'openssh-client'
        ] }

        'Ubuntu': { $os_packages = [
          'apt-file', 'molly-guard', 'vim-puppet', 'vim-addon-manager', 'vim-scripts', 'aptitude',
          'dnsutils', 'gnupg', 'vim', 'openssh-client'
        ] }

        'centos': { $os_packages = [
          'bind-utils', 'gnupg2', 'vim-enhanced', 'openssh'
        ] }
        default: { $os_packages = [] }
    }

    package { $base_packages:
        ensure => installed,
    }

    package { $os_packages:
        ensure => installed,
    }
}


