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
class nova::params {
    $basedir = $::operatingsystem ? {
        default => '/etc/nova',
    }

    $configfile = $::operatingsystem ? {
        default => '/etc/nova/nova.conf',
    }

    $group = $::operatingsystem ? {
        default => 'nova',
    }

    $hasstatus = $::operatingsystem ? {
        default => true,
    }

    $mode = $::operatingsystem ? {
        default => '0644',
    }

    $owner = $::operatingsystem ? {
        default => 'nova',
    }

    $packagename = $::operatingsystem ? {
        default => 'nova-compute',
    }

    $processname = $::operatingsystem ? {
        default => 'nova-compute',
    }

    $servicename = $::operatingsystem ? {
        default => 'nova-compute',
    }

    $varlib = $::operatingsystem ? {
        default => '/var/lib/nova',
    }

    $db = $nova_db ? {
        ''      => 'mysql',
        default => $nova_db,
    }

    $db_name = $nova_db_name ? {
        ''      => 'nova',
        default => $nova_db_name,
    }

    $db_password = $nova_db_password ? {
        ''      => '',
        default => $nova_db_password,
    }

    $db_server = $nova_db_server ? {
        ''      => 'localhost',
        default => $nova_db_server,
    }

    $db_user = $nova_db_user ? {
        ''      => 'novadbadmin',
        default => $nova_db_user,
    }

    if ($db_password == '') {
        fail('You must assign a default password using \'\$nova_db_password\'')
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
