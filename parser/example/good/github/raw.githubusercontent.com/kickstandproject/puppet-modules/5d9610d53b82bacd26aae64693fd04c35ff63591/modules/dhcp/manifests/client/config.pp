#
# puppet-modules: The Kickstand Project
#
# Copyright (C) 2011, Polybeacon, Inc.
#
# Paul Belanger <paul.belanger@polybeacon.com>
#
# See http://kickstand-project.org for more information about
# the Kickstand project. Please do not directly contact any
# of the maintainers of this project for assistance; the
# project provides a web site, forums and IRC channels for
# your use.
#
# This program is free software, distributed under the terms
# of the GNU General Public License Version 2. See the LICENSE
# file at the top of the source tree.
#
class dhcp::client::config {
    include dhcp::common::config

    file { "${dhcp::params::client::basedir}/dhclient-enter-hooks.d":
        ensure  => directory,
        require => File[$dhcp::params::client::basedir],
    }

    file { "${dhcp::params::client::basedir}/dhclient-exit-hooks.d":
        ensure  => directory,
        require => File[$dhcp::params::client::basedir],
    }

    file { $dhcp::params::client::configfile:
        ensure  => present,
        content => template('dhcp/etc/dhcp/dhclient.conf.erb'),
        require => File[$dhcp::params::client::basedir],
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
