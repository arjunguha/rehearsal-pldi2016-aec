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
define monitor::function::process(
  $process,
  $description = '',
  $ensure = present,
) {
  if ($::monitor == 'yes') {
    require nsca::client
    include monitor::params

    if ($description != '') {
      $description_real = $description
    } else {
      $description_real = "Check Process ${process}"
    }

    File {
      group => $nsca::params::group,
      mode  => $nsca::params::mode,
      owner => $nsca::params::owner,
    }

    nagios::function::service::nsca { "check_procs_${process}!1!1":
      ensure      => $ensure,
      description => $description_real,
      server      => $monitor::client::server,
    }

    nagios::command { "check_procs_${process}":
      command_line  => "/usr/lib/nagios/plugins/check_procs -C ${process} -w '\$ARG1$:' -c '\$ARG2$:'"
    }
  }
}

# vim:sw=2:ts=2:expandtab:textwidth=79
