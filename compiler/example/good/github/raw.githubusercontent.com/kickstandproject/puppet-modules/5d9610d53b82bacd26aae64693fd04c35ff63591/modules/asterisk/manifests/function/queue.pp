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
define asterisk::function::queue(
  $members = [],
  $settings = {},
) {
  require asterisk::server
  $defaults = {
    'strategy' => 'ringall',
  }

  $settings_real = merge($defaults, $settings)

  $base = "${asterisk::params::basedir}/queues.conf.d/includes"

  file { "$base/${name}":
    ensure  => directory,
    notify  => Exec['asterisk-module-reload-queues.conf'],
    purge   => true,
    recurse => true,
    require => File[$base],
  }

  file { "$base/${name}.conf":
    ensure  => present,
    content => template('asterisk/etc/asterisk/queues.conf.d/includes/template.conf.erb'),
    notify  => Exec['asterisk-module-reload-queues.conf'],
    require => File[$base],
  }
}

# vim:sw=2:ts=2:expandtab:textwidth=79
