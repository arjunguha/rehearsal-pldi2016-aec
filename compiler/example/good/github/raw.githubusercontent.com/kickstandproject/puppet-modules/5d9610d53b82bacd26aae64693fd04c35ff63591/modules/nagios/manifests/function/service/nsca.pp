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
define nagios::function::service::nsca (
    $description,
    $server,
    $check_command = false,
    $ensure = 'present',
    $use_active = 'generic-service-active',
    $use_passive = 'generic-service-passive'
) {
    require nagios::client
    include nagios::params

    if ($::fqdn != $server) {
        nagios::function::service::local { $name:
            ensure          => $ensure,
            check_command   => $check_command,
            description     => $description,
            hostgroup_name  => 'all',
            use             => $use_active,
        }


        @@nagios_service { "@@${name} on ${fqdn}":
            ensure              => $ensure,
            host_name           => $::fqdn,
            notify              => Class['nagios::common::service'],
            require             => File["${nagios::params::configdir}/services/passive"],
            service_description => $description,
            tag                 => $server,
            target              => "${nagios::params::configdir}/services/passive/${name}.on.${fqdn}.cfg",
            use                 => $use_passive,
        }

        @@file { "${nagios::params::configdir}/services/passive/${name}.on.${fqdn}.cfg":
            ensure  => $ensure,
            group   => $nagios::params::group,
            mode    => $nagios::params::mode,
            owner   => $nagios::params::owner,
            require => File["${nagios::params::configdir}/services/passive"],
            tag     => $server,
        }
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
