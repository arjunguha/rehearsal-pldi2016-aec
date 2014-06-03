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
define polycom-provision::function::site(
  $content = template('polycom-provision/var/lib/polycom-provision/site.cfg.erb'),
) {
  require polycom-provision::server

  file { "${polycom-provision::params::basedir}/site.cfg":
    ensure  => present,
    content => $content,
    require => File[$polycom-provision::params::basedir],
  }
}

# vim:sw=2:ts=2:expandtab:textwidth=79
