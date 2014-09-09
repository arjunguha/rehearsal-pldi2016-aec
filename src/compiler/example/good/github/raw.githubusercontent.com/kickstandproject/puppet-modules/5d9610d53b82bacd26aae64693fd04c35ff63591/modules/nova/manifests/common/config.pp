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
class nova::common::config {
    file { $nova::params::basedir:
        ensure  => directory,
        require => Class['nova::common::install'],
    }

    file { $nova::params::configfile:
        ensure  => present,
        content => template('nova/etc/nova/nova.conf.erb'),
        notify  => Class['nova::common::service'],
        require => File[$nova::params::basedir],
    }

    file { $nova::params::varlib:
        ensure  => directory,
        purge   => true,
        recurse => true,
        require => Class['nova::common::install'],
    }

    file { [
        "${nova::params::varlib}/buckets",
        "${nova::params::varlib}/CA",
        "${nova::params::varlib}/images",
        "${nova::params::varlib}/instances",
        "${nova::params::varlib}/keys",
        "${nova::params::varlib}/networks",
        "${nova::params::varlib}/tmp"
    ]:
        ensure  => directory,
        require => File[$nova::params::varlib],
    }

}

# vim:sw=4:ts=4:expandtab:textwidth=79
