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
define polycom-provision::function::sip-basic(
    $address,
) {
    require polycom-provision::server

    $split = split($address, ':')
    $address_real = $split[0]

    if ($split[1]) {
        $port_real = $split[1]
    } else {
        $port_real = '5060'
    }

    File {
        group   => $polycom-provision::params::group,
        mode    => $polycom-provision::params::mode,
        owner   => $polycom-provision::params::owner,
    }

    file { "${polycom-provision::params::basedir}/sip-basic.cfg":
        ensure  => present,
        content => template('polycom-provision/var/lib/polycom-provision/sip-basic.cfg.erb'),
        require => File[$polycom-provision::params::basedir],
    }

    file { "${polycom-provision::params::basedir}/legacy/sip-basic.cfg":
        ensure  => present,
        content => template('polycom-provision/var/lib/polycom-provision/legacy/sip-basic.cfg.erb'),
        require => File["${polycom-provision::params::basedir}/legacy"],
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
