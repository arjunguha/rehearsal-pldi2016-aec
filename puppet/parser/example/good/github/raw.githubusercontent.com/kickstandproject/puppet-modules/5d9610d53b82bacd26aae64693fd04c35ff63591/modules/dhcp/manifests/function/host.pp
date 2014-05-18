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
define dhcp::function::host(
    $address,
    $options = {},
) {
    require dhcp::server

    if (!defined(Common::Function::Concat["${$dhcp::params::server::basedir}/hosts"])) {
        common::function::concat { "${dhcp::params::server::basedir}/hosts":
            notify  => Class['dhcp::server::service'],
            require => File[$dhcp::params::server::basedir],
        }

        common::function::concat::fragment { 'dhcpd.conf-include':
            target  => $dhcp::params::server::configfile,
            content => template('dhcp/etc/dhcp/include.erb'),
            order   => 01,
        }
    }

    common::function::concat::fragment { "dhcp_function_host_${name}":
        target  => "${dhcp::params::server::basedir}/hosts",
        content => template('dhcp/etc/dhcp/host.erb'),
        order   => 02,
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
