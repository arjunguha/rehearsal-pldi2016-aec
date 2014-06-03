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
class keystone::params {
    $basedir = $::operatingsystem ? {
        default => '/etc/keystone',
    }

    $group = $::operatingsystem ? {
        default => 'keystone',
    }

    $hasstatus = $::operatingsystem ? {
        default => true,
    }

    $mode = $::operatingsystem ? {
        default => '0644',
    }

    $owner = $::operatingsystem ? {
        default => 'keystone',
    }

    $packagename = $::operatingsystem ? {
        default => 'keystone',
    }

    $processname = $::operatingsystem ? {
        default => 'keystone',
    }

    $servicename = $::operatingsystem ? {
        default => 'keystone',
    }

    $varlib = $::operatingsystem ? {
        default => '/var/lib/keystone',
    }

    $db = $keystone_db ? {
        ''      => 'mysql',
        default => $keystone_db,
    }

    $db_name = $keytone_db_name ? {
        ''      => 'keystone',
        default => $keystone_db_name,
    }

    $db_password = $keystone_db_password ? {
        ''      => '',
        default => $keystone_db_password,
    }

    $db_server = $keystone_db_server ? {
        ''      => 'localhost',
        default => $keystone_db_server,
    }

    $db_user = $keystone_db_user ? {
        ''      => 'keystonedbadmin',
        default => $keystone_db_user,
    }

    if ($db_password == '') {
        fail('You must assign a default password using \'\$keystone_db_password\'')
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
