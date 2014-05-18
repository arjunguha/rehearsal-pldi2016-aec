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
class nagios::web::common::config {
    include nagios::params
    include apache::params

    file { "${nagios::params::basedir}/stylesheets":
        ensure  => directory,
        require => File[$nagios::params::basedir],
    }

    file { "${nagios::params::basedir}/cgi.cfg":
        ensure  => present,
        content => template('nagios/etc/nagios3/cgi.cfg.erb'),
        notify  => Class['nagios::common::service'],
        require => File[$nagios::params::basedir],
    }

    file { "${apache::params::configdir}/conf.d/nagios3.conf":
        ensure  => absent,
        require => Class['apache::common::config'],
    }

    apache::function::virtualhost { $::fqdn:
        content => template('nagios/etc/apache2/conf.d/nagios3.conf.erb'),
    }

    apache::function::htdigest { $nagios::web::params::hostname:
        authname    => 'default',
        content     => template('nagios/etc/apache2/conf.d/htdigest.conf.erb'),
        password    => $nagios::web::params::password,
        username    => $nagios::web::params::username,
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
