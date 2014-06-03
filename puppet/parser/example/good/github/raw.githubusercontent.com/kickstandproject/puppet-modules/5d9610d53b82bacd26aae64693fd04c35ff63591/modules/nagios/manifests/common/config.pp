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
class nagios::common::config {
    file { $nagios::params::basedir:
        ensure  => directory,
        force   => true,
        purge   => true,
        recurse => true,
        require => Class['nagios::common::install'],
    }

    common::function::concat { $nagios::params::configfile:
    }

    common::function::concat::fragment { 'nagios.cfg':
        target  => $nagios::params::configfile,
        content => template('nagios/etc/nagios3/nagios.cfg.erb'),
        order   => 01,
        require => File[$nagios::params::basedir],
    }

    file { "${nagios::params::basedir}/resource.cfg":
        ensure  => present,
        content => template('nagios/etc/nagios3/resource.cfg.erb'),
        notify  => Class['nagios::common::service'],
        require => File[$nagios::params::basedir],
    }

    file { $nagios::params::configdir:
        ensure  => directory,
        force   => true,
        purge   => true,
        recurse => true,
        require => File[$nagios::params::basedir],
    }

    file { [
        "${nagios::params::configdir}/commands",
        "${nagios::params::configdir}/hostgroups",
        "${nagios::params::configdir}/hosts",
        "${nagios::params::configdir}/services",
    ]:
        ensure  => directory,
        force   => true,
        notify  => Class['nagios::common::service'],
        purge   => true,
        recurse => true,
        require => File[$nagios::params::configdir],
    }

    file { "${nagios::params::configdir}/commands/general.cfg":
        ensure  => present,
        content => template('nagios/etc/nagios3/conf.d/commands/general.cfg.erb'),
        require => File["${nagios::params::configdir}/commands"],
    }

    file { "${nagios::params::configdir}/contacts.cfg":
        ensure  => present,
        content => template('nagios/etc/nagios3/conf.d/contacts.cfg.erb'),
        require => File[$nagios::params::configdir],
    }

    file { "${nagios::params::configdir}/hosts/generic.cfg":
        ensure  => present,
        content => template('nagios/etc/nagios3/conf.d/hosts/generic.cfg.erb'),
        require => File["${nagios::params::configdir}/hosts"],
    }

    file { "${nagios::params::configdir}/hostgroups/all.cfg":
        ensure  => present,
        content => template('nagios/etc/nagios3/conf.d/hostgroups/all.cfg.erb'),
        require => File["${nagios::params::configdir}/hostgroups"],
    }

    file { [
        "${nagios::params::configdir}/services/active",
        "${nagios::params::configdir}/services/passive",
    ]:
        ensure  => directory,
        force   => true,
        purge   => true,
        recurse => true,
        require => File["${nagios::params::configdir}/services"],
    }

    file { "${nagios::params::configdir}/services/generic.cfg":
        ensure  => present,
        content => template('nagios/etc/nagios3/conf.d/services/generic.cfg.erb'),
        require => File["${nagios::params::configdir}/services"],
    }

    file { "${nagios::params::configdir}/timeperiods.cfg":
        ensure  => present,
        content => template('nagios/etc/nagios3/conf.d/timeperiods.cfg.erb'),
        require => File[$nagios::params::configdir],
    }

    file { $nagios::params::plugindir:
        ensure  => present,
        require => Class['nagios::common::install'],
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
