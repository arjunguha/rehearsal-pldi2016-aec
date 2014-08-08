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
class glance::common::install {
    package { $glance::params::packagename:
        ensure  => present,
    }

    common::function::database { $glance::params::packagename:
        notify      => Exec['glance-manage-db-sync'],
        password    => $glance::params::db_password,
        server      => $glance::params::db_server,
        table       => $glance::params::db_name,
        type        => $glance::params::db,
        user        => $glance::params::db_user,
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
