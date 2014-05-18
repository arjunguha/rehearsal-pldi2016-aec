class puppet_support {
    package { 'rubygems': ensure     => installed }
    package { 'augeas-tools': ensure => installed }

    exec { 'gem install puppet-lint':
        path    => '/usr/bin:/bin:/usr/sbin',
        unless  => 'gem list --local | grep "^puppet-lint "',
        require => Package[rubygems]
    }

    exec { 'gem install puppet-module':
        path    => '/usr/bin:/bin:/usr/sbin',
        unless  => 'gem list --local | grep "^puppet-module"',
        require => Package[rubygems]
    }
}
