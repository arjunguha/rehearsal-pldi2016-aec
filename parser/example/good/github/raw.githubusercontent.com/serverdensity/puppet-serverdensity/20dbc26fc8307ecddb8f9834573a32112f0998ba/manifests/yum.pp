# == Class: serverdensity_agent::yum
#
# Sets up the yum repository for the agent
#
# === Authors
#
# Server Density <hello@serverdensity.com>
#
# === Copyright
#
# Copyright 2014 Server Density
#

class serverdensity_agent::yum {
    $repo_baseurl = 'http://www.serverdensity.com/downloads/linux/redhat/'
    $repo_keyurl = 'https://www.serverdensity.com/downloads/boxedice-public.key'

    yumrepo { 'serverdensity_agent':
        baseurl  => $repo_baseurl,
        gpgkey   => $repo_keyurl,
        descr    => 'Server Density',
        enabled  => 1,
        gpgcheck => 1,
    }
    # install SD agent package
    package { 'sd-agent':
        ensure   => present,
        require  => Yumrepo['serverdensity_agent']
    }
}
