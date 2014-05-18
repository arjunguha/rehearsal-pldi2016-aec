define apt::ppa($ppa_user, $ppa_name, $keyid, $ubuntu_release, $ensure = 'present') {
    case $ensure {
        present: {
            file { "Add $ppa_user/$ppa_name to sources.list.d":
                path    => "/etc/apt/sources.list.d/$ppa_user-$ppa_name.list",
                content => template('apt/sources.list.erb'),
            }

            apt::key { "Add $keyid to keystore":
                ensure => present,
                keyid  => $keyid,
            }
        }

        default: {
            fail "Invalid 'ensure' value '$ensure' for apt::ppa"
        }
    }
}

# http://projects.puppetlabs.com/projects/puppet/wiki/Apt_Keys_Patterns
define apt::key($keyid, $ensure, $keyserver = 'keyserver.ubuntu.com') {
        case $ensure {
                present: {
                        exec { "Import $keyid to apt keystore":
                                path        => '/bin:/usr/bin',
                                environment => 'HOME=/root',
                                command     => "gpg --keyserver $keyserver --recv-keys $keyid && gpg --export --armor $keyid | apt-key add -",
                                user        => root,
                                group       => root,
                                unless      => "apt-key list | grep $keyid",
                                logoutput   => on_failure,
                        }
                }
                absent:  {
                        exec { "Remove $keyid from apt keystore":
                                path        => '/bin:/usr/bin',
                                environment => 'HOME=/root',
                                command     => "apt-key del $keyid",
                                user        => root,
                                group       => root,
                                onlyif      => "apt-key list | grep $keyid",
                        }
                }
                default: {
                        fail "Invalid 'ensure' value '$ensure' for apt::key"
                }
        }
}
