class ruby {
    # Ensure we have ruby
    package { "ruby1.9.1":
        ensure => latest,
        require => Exec['apt-get update']
    }

    # Ensure we can install gems
    package { 'rubygems':
        ensure => 'latest'
    }

    # Install gems
    package { 'compass':
        provider => 'gem',
        ensure => 'latest'
    }
    package { 'susy':
        provider => 'gem',
        ensure => 'latest'
    }
    package { 'sass-globbing':
        provider => 'gem',
        ensure => 'latest'
    }
    package { 'capistrano':
        provider => 'gem',
        ensure => 'latest'
    }
    package { 'railsless-deploy':
        provider => 'gem',
        ensure => 'latest'
    }
}