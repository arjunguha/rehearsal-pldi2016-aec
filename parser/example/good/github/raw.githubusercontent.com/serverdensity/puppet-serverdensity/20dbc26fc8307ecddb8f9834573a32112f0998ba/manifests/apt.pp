# == Class: serverdensity_agent::apt
#
# Sets up the apt repository for the agent
#
# === Authors
#
# Server Density <hello@serverdensity.com>
#
# === Copyright
#
# Copyright 2014 Server Density
#

class serverdensity_agent::apt {
    $repo_baseurl = 'http://www.serverdensity.com/downloads/linux/deb'
    $repo_keyurl = 'https://www.serverdensity.com/downloads/boxedice-public.key'

    apt::source { 'serverdensity_agent':
        location    => $repo_baseurl,
        release     => 'all',
        repos       => 'main',
        key         => '13C2E6F8',
        key_source  => $repo_keyurl,
        include_src => false
    }
    package {
            'sd-agent':
                    ensure  => 'present',
                    require => Apt::Source['serverdensity_agent'],
    }
}
