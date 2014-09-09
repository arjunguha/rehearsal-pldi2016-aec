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
class mantisbt::params {
    $basedir = $::operatingsystem ? {
        default => '/etc/mantis',
    }

    $configfile = $::operatingsystem ? {
        default => '/etc/mantis',
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
        default => 'mantis',
    }

    $processname = $::operatingsystem ? {
        default => 'mantis',
    }

    $servicename = $::operatingsystem ? {
        default => 'mantis',
    }

    $db = $mantisbt_db ? {
        ''      => 'mysql',
        default => $mantisbt_db,
    }

    $db_name = $mantisbt_db_name ? {
        ''      => 'mantisbt',
        default => $mantisbt_db_name,
    }

    $db_password = $mantisbt_db_password ? {
        ''      => '',
        default => $mantisbt_db_password,
    }

    $db_server = $mantisbt_db_server ? {
        ''      => 'localhost',
        default => $mantisbt_db_server,
    }

    $db_user = $mantisbt_db_user ? {
        ''      => 'mantisbtdbadmin',
        default => $mantisbt_db_user,
    }

    $hostname = $mantisbt_hostname ? {
        ''      => $::fqdn,
        default => $mantisbt_hostname,
    }

    if ($db_password == '') {
        fail('You must assign a default password using \'\$mantisbt_db_password\'')
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
