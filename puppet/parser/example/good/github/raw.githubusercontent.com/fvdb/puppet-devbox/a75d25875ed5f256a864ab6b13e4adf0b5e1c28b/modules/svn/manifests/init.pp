class svn {
    # Install svn
    package { ["subversion", "subversion-tools"]:
        ensure => latest,
        require => Exec['apt-get update']
    }

    # Force the configuration directory to be initialized
    file { "/home/vagrant/.subversion":
        ensure => "directory",
        owner => "vagrant",
        group => "vagrant"
    }

    # Set the config file
    file { "/home/vagrant/.subversion/config":
        ensure => file,
        replace => true,
        owner => "vagrant",
        group => "vagrant",
        source => "puppet:///modules/svn/config",
        require => File["/home/vagrant/.subversion"]
    }

    # Set the servers file
    file { "/home/vagrant/.subversion/servers":
        ensure => file,
        replace => true,
        owner => "vagrant",
        group => "vagrant",
        source => "puppet:///modules/svn/servers",
        require => File["/home/vagrant/.subversion"]
    }
}
