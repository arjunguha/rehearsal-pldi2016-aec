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
class dhcp::server(
    $authoritative = true,
    $interfaces = '',
    $options = {}
) {
    $defaults = {
        'ddns-update-style'     => 'interim',
        'log-facility'          => 'local7',
        'default-lease-time'    => '3600',
        'max-lease-time'        => '86400',
    }

    $options_real = merge($defaults, $options)

    if ($authoritative) {
        $authoritative_real = 'authoritative'
    }

    if ($interfaces != '') {
        $interfaces_real = $interfaces
    } else {
        $interfaces_real = 'eth0'
    }

    include dhcp::client
    include dhcp::params::server
    include dhcp::server::init
}

# vim:sw=4:ts=4:expandtab:textwidth=79
