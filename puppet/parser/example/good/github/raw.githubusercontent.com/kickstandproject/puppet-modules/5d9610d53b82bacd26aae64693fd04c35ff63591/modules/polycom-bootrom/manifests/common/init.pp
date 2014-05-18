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
class polycom-bootrom::common::init {
    include polycom-bootrom::params
    include polycom-bootrom::common::install
    include polycom-bootrom::common::config
    include polycom-bootrom::common::service

    File {
        group   => $polycom-bootrom::params::group,
        mode    => $polycom-bootrom::params::mode,
        owner   => $polycom-bootrom::params::owner,
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
