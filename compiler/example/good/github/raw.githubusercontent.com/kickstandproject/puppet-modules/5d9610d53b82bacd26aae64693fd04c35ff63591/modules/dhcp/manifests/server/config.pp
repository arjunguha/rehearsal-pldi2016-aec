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
class dhcp::server::config {
    include dhcp::common::config

    common::function::concat { $dhcp::params::server::configfile:
        notify  => Class['dhcp::server::service'],
        require => File[$dhcp::params::server::basedir],
    }

    common::function::concat::fragment { 'dhcpd.conf-header':
        target  => $dhcp::params::server::configfile,
        content => template('dhcp/etc/dhcp/dhcpd.conf.erb'),
        order   => 01,
    }

    file { $dhcp::params::server::defaultfile:
        ensure  => present,
        content => template('dhcp/etc/default/isc-dhcp-server.erb'),
        notify  => Class['dhcp::server::service'],
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
