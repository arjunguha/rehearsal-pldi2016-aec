class git ($gitUser, $gitEmail) {
    # Install git
    package { "git":
        ensure => latest,
        require => Exec['apt-get update']
    }

    # Set the configuration
    file { "/home/vagrant/.gitconfig":
        ensure => file,
        replace => false,
        owner => "vagrant",
        group => "vagrant",
        source => "puppet:///modules/git/gitconfig"
    }

    # Set the username and password
    exec { "git.username":
        command => "sed -i 's/name = __NAME__/name = $gitUser/' /home/vagrant/.gitconfig",
        onlyif => "grep \"name = __NAME__\" /home/vagrant/.gitconfig",
        require => File['/home/vagrant/.gitconfig']
    }
    exec { "git.email":
        command => "sed -i 's/email = __EMAIL__/email = $gitEmail/' /home/vagrant/.gitconfig",
        onlyif => "grep \"email = __EMAIL__\" /home/vagrant/.gitconfig",
        require => File['/home/vagrant/.gitconfig']
    }

    # Set ignores
    file { "/home/vagrant/.gitignore":
        ensure => file,
        replace => false,
        owner => "vagrant",
        group => "vagrant",
        source => "puppet:///modules/git/gitignore"
    }
}
