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
class nsca::server::init {
    include nsca::common::init
    include nsca::server::install
    include nsca::server::config
    include nsca::server::service
    include nsca::server::firewall

    File            <<| tag == $::fqdn |>>
    Nagios_command  <<| tag == $::fqdn |>>
    Nagios_host     <<| tag == $::fqdn |>>
    Nagios_service  <<| tag == $::fqdn |>>
}

# vim:sw=4:ts=4:expandtab:textwidth=79
