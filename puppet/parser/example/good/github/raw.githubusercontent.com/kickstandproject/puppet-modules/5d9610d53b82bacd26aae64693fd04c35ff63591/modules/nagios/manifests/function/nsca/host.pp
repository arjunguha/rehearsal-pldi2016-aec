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
define nagios::function::nsca::host(
    $server,
    $address = 'localhost',
    $ensure = present,
    $use_active = 'generic-host-active',
    $use_passive = 'generic-host-passive'
) {
    require nsca::client

    nagios_host { $name:
        ensure  => $ensure,
        address => $address,
        notify  => Class['nagios::common::service'],
        require => File["${nagios::params::configdir}/hosts"],
        target  => "${nagios::params::configdir}/hosts/${name}.cfg",
        use     => $use_active,
    }

    file { "${nagios::params::configdir}/hosts/${name}.cfg":
        ensure  => $ensure,
        before  => Nagios_host[$name],
        group   => $nagios::params::group,
        mode    => $nagios::params::mode,
        owner   => $nagios::params::owner,
    }

    if ($name != $server) {
        @@nagios_host { "@@${name}":
            ensure      => $ensure,
            address     => $address,
            alias       => $name,
            host_name   => $name,
            notify      => Class['nagios::common::service'],
            require     => File["${nagios::params::configdir}/hosts"],
            tag         => $server,
            target      => "${nagios::params::configdir}/hosts/passive-${name}.cfg",
            use         => $use_passive,
        }

        @@file { "${nagios::params::configdir}/hosts/passive-${name}.cfg":
            ensure  => $ensure,
            group   => $nagios::params::group,
            mode    => $nagios::params::mode,
            owner   => $nagios::params::owner,
            tag     => $server,
        }
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
