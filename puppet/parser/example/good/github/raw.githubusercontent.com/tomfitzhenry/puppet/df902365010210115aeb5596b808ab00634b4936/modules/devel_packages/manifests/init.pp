class devel_packages {
    $devel_packages = [

        'subversion',
        'mercurial',

        'openjdk-6-jdk',
        'openjdk-6-source',
        'openjdk-7-jdk',

        'visualvm',
        'maven2',
        'scala',

        'golang',
        'golang-doc',

        'ghc',
        'ghc-doc',

        'octave',

        'exuberant-ctags',

        'build-essential',
        'libssl-dev',
        'e2fslibs-dev',

    ]

    exec { 'apt_update':
        command  => '/usr/bin/apt-get -q -q update',

        # exec outputs "Executed succesfully" on the default loglevel.
        # This spam is undesirable. Overriding the loglevel fixes this.
        loglevel => info,
    }

    package { $devel_packages:
        ensure  => installed,
        require => Exec[apt_update]
    }

}
