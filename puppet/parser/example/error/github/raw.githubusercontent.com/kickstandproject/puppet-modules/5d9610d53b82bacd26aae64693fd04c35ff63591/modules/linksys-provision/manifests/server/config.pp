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
class linksys-provision::server::config {
    require apache::server
    require tftp::server

    file { $linksys-provision::params::server::basedir:
        ensure  => directory,
        purge   => true,
        recurse => true,
    }

    file { "${$linksys-provision::params::server::basedir}/spa942-site.xml":
        ensure  => present,
        content => template('linksys-provision/var/lib/linksys-provision/spa942-site.xml.erb'),
        require => File[$linksys-provision::params::server::basedir],
    }

    file { "${linksys-provision::params::server::basedir}/configs":
        ensure  => directory,
        purge   => true,
        recurse => true,
        require => File[$linksys-provision::params::server::basedir],
    }

    file { "${linksys-provision::params::server::basedir}/firmwares":
        ensure  => directory,
        purge   => true,
        recurse => true,
        require => File[$linksys-provision::params::server::basedir],
    }

    file { "${apache::params::rootdir}/${$linksys-provision::params::server::hostname}/html/linksys":
        ensure  => link,
        require => File["${apache::params::rootdir}/${$linksys-provision::params::server::hostname}/html"],
        target  => $linksys-provision::params::server::basedir,
    }

    file { "${tftp::params::server::basedir}/spa942.cfg":
        ensure  => present,
        content => template('linksys-provision/var/lib/tftpboot/spa942.cfg.erb'),
        require => File[$tftp::params::server::basedir],
    }

    linksys-provision::function::firmware { 'spa942.bin': }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
