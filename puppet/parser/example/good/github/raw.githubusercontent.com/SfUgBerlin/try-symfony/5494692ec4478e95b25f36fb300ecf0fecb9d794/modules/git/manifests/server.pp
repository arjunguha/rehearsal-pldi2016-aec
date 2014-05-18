class git::server inherits git::client {

    #
    # Documentation on this class
    #
    # Including this class will install git, the git-daemon, ensure the
    # service is running
    #

    package { "git-daemon-run":
        ensure => installed
    }

    #service { "git":
    #    enable => true,
    #    ensure => running,
    #    require => Package["git-daemon-run"],
    #    notify => Service["xinetd"]
    #}

    #service { "xinetd":
    #    enable => true,
    #    ensure => running
    #}

    file { "/srv/git/":
        ensure => directory,
        mode => 755
    }

    file { "/usr/local/bin/git_init_script":
        owner => "root",
        group => "root",
        mode => 750,
        source => [
            #"puppet://$server/private/$domain/git/git_init_script",
            #"puppet://$server/files/git/git_init_script",
            "puppet://$server/git/git_init_script"
        ]
    }
}
