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
class asterisk::server::init {
    include asterisk::server::install
    include asterisk::server::config
    include asterisk::server::service
    include asterisk::server::command
    include asterisk::server::monitor
    include asterisk::server::firewall

    File {
        group   => $asterisk::params::group,
        mode    => $asterisk::params::mode,
        owner   => $asterisk::params::owner,
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
