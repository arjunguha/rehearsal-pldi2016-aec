class dev {
    package { 'acl':
        ensure => installed
    }
    package { 'curl':
        ensure => installed
    }
    package { 'git':
        ensure => installed
    }
}
