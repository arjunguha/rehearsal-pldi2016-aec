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
class glance::common::init {
    include glance::params
    include glance::common::install
    include glance::common::config
    include glance::common::service
    include glance::common::command

    File {
        group   => $glance::params::group,
        mode    => $glance::params::mode,
        owner   => $glance::params::owner,
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
