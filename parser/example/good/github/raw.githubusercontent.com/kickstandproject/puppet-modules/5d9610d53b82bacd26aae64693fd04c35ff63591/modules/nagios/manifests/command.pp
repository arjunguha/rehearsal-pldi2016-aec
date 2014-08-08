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
define nagios::command(
    $command_line,
    $ensure = present,
) {
    include nagios::params

    nagios_command { $name:
        ensure          => $ensure,
        command_line    => $command_line,
        notify          => Class['nagios::common::service'],
        target          => "${nagios::params::configdir}/commands/${name}.cfg",
    }

    file { "${nagios::params::configdir}/commands/${name}.cfg":
        ensure  => $ensure,
        before  => Nagios_command[$name],
        group   => $nagios::params::group,
        mode    => $nagios::params::mode,
        owner   => $nagios::params::owner,
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
