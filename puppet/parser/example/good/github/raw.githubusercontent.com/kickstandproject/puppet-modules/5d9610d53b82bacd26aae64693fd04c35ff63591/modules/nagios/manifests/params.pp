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
class nagios::params {
    $basedir = $::operatingsystem ? {
        default => '/etc/nagios3',
    }

    $configdir = $::operatingsystem ? {
        default => '/etc/nagios3/conf.d',
    }

    $configfile = $::operatingsystem ? {
        default => '/etc/nagios3/nagios.cfg',
    }

    $group = $::operatingsystem ? {
        default => 'root',
    }

    $hasstatus = $::operatingsystem ? {
        default => true,
    }

    $mode = $::operatingsystem ? {
        default => '0644',
    }

    $owner = $::operatingsystem ? {
        default => 'root',
    }

    $packagename = $::operatingsystem ? {
        default => [
            'nagios3-core',
            'nagios-plugins-extra'
        ],
    }

    $processname = $::operatingsystem ? {
        default => 'nagios',
    }

    $servicename = $::operatingsystem ? {
        default => 'nagios3',
    }

    $plugindir = $::operatingsystem ? {
        default => '/usr/lib/nagios/plugins',
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
