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
class nsca::client::config {
    include nsca::common::config

    file { $nsca::params::client::configfile:
        ensure  => present,
        content => template('nsca/etc/send_nsca.cfg.erb'),
        require => Class['nsca::client::install'],
    }

    nagios_command { 'submit_ocsp':
        ensure          => present,
        command_line    => "${nagios::params::plugindir}/submit_ocsp \$HOSTNAME\$ '\$SERVICEDESC\$' \$SERVICESTATEID\$ '\$SERVICEOUTPUT\$'",
        target          => "${nagios::params::configdir}/commands/submit_ocsp.cfg",
        notify          => Class['nagios::common::service'],
        require         => File["${nagios::params::configdir}/commands/submit_ocsp.cfg"],
    }

    file { "${nagios::params::configdir}/commands/submit_ocsp.cfg":
        ensure  => present,
        require => File["${nagios::params::configdir}/commands"],
    }

    nagios_command { 'submit_ochp':
        ensure          => present,
        command_line    => "${nagios::params::plugindir}/submit_ochp \$HOSTNAME\$ \$HOSTSTATE\$ '\$HOSTOUTPUT\$'",
        target          => "${nagios::params::configdir}/commands/submit_ochp.cfg",
        notify          => Class['nagios::common::service'],
        require         => File["${nagios::params::configdir}/commands/submit_ochp.cfg"],
    }

    file { "${nagios::params::configdir}/commands/submit_ochp.cfg":
        ensure  => present,
        require => File["${nagios::params::configdir}/commands"],
    }

    file { "${nagios::params::plugindir}/submit_ocsp":
        ensure  => present,
        content => template('nsca/usr/lib/nagios/plugins/submit_ocsp.erb'),
        mode    => '0755',
        require => File[$nagios::params::plugindir],
    }

    file { "${nagios::params::plugindir}/submit_ochp":
        ensure  => present,
        content => template('nsca/usr/lib/nagios/plugins/submit_ochp.erb'),
        mode    => '0755',
        require => File[$nagios::params::plugindir],
    }

}

# vim:sw=4:ts=4:expandtab:textwidth=79
