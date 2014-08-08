#
# puppet-modules: The Kickstand Project
#
# Copyright (C) 2012, PolyBeacon, Inc.
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
class asterisk::dahdi::server::init {
  include asterisk::dahdi::server::install
  include asterisk::dahdi::server::config
  include asterisk::dahdi::server::command

  File {
    group => $asterisk::params::dahdi::group,
    mode  => $asterisk::params::dahdi::mode,
    owner => $asterisk::params::dahdi::owner,
  }
}

# vim:sw=2:ts=2:expandtab:textwidth=79
