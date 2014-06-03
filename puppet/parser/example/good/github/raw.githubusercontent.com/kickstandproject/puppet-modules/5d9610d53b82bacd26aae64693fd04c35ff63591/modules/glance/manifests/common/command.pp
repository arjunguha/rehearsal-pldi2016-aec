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
class glance::common::command {
    exec { 'glance-manage-db-sync':
        before      => Class['glance::common::service'],
        command     => 'glance-manage version_control 0',
        notify      => Exec['glance-manage-db-sync-real'],
        refreshonly => true,
        require     => Class['glance::common::config'],
        user        => $glance::params::owner,
    }

    exec { 'glance-manage-db-sync-real':
        before      => Class['glance::common::service'],
        command     => 'glance-manage db_sync',
        refreshonly => true,
        require     => Class['glance::common::config'],
        user        => $glance::params::owner,
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
