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
class polycom-provision::server::config {
    require apache::server
    require polycom-ucs::params
    include polycom-provision::params

    file { $polycom-provision::params::basedir:
        ensure  => directory,
    }

    file { "${polycom-provision::params::basedir}/000000000000.cfg":
        ensure  => present,
        content => template('polycom-provision/var/lib/polycom-provision/000000000000.cfg.erb'),
        require => File[$polycom-provision::params::basedir],
    }

    file { "${polycom-provision::params::basedir}/configs":
        ensure  => directory,
        purge   => true,
        recurse => true,
        require => File[$polycom-provision::params::basedir],
    }

    file { "${polycom-provision::params::basedir}/contacts":
        ensure  => directory,
        purge   => true,
        recurse => true,
        require => File[$polycom-provision::params::basedir],
    }

    file { "${polycom-provision::params::basedir}/features.cfg":
        ensure  => present,
        content => template('polycom-provision/var/lib/polycom-provision/features.cfg.erb'),
        require => File[$polycom-provision::params::basedir],
    }

    file { "${polycom-provision::params::basedir}/firmwares":
        ensure  => directory,
        purge   => true,
        recurse => true,
        require => File[$polycom-provision::params::basedir],
    }

    file { "${polycom-provision::params::basedir}/legacy":
        ensure  => directory,
        purge   => true,
        recurse => true,
        require => File[$polycom-provision::params::basedir],
    }

    file { "${polycom-provision::params::basedir}/legacy/defaults.cfg":
        ensure  => present,
        content => template('polycom-provision/var/lib/polycom-provision/legacy/defaults.cfg.erb'),
        require => File["${polycom-provision::params::basedir}/legacy"],
    }

    file { "${polycom-provision::params::basedir}/images":
        ensure  => link,
        target  => "${polycom-ucs::params::basedir}/images",
        require => File[$polycom-provision::params::basedir],
    }

    file { "${polycom-provision::params::basedir}/logs":
        ensure  => directory,
        group   => 'www-data',
        mode    => '0644',
        owner   => 'www-data',
        require => File[$polycom-provision::params::basedir],
    }

    $legacy_bootroms = [
        'bootrom.ld',
        '2201-06642-001.bootrom.ld',
        '2345-11000-001.bootrom.ld',
        '2345-11300-001.bootrom.ld',
        '2345-11300-010.bootrom.ld',
        '2345-11402-001.bootrom.ld',
        '2345-11500-001.bootrom.ld',
        '2345-11500-010.bootrom.ld',
        '2345-11500-020.bootrom.ld',
        '2345-11500-030.bootrom.ld',
        '2345-11500-040.bootrom.ld',
        '2345-11600-001.bootrom.ld',
        '2345-11605-001.bootrom.ld',
        '2345-17960-001.bootrom.ld',
    ]

    polycom-provision::function::bootrom { $legacy_bootroms:
        legacy => 'yes',
    }

    $firmwares = [
        '2345-12200-001.sip.ld',
        '2345-12200-002.sip.ld',
        '2345-12200-004.sip.ld',
        '2345-12200-005.sip.ld',
        '2345-12360-001.sip.ld',
        '2345-12365-001.sip.ld',
        '2345-12375-001.sip.ld',
        '2345-12450-001.sip.ld',
        '2345-12500-001.sip.ld',
        '2345-12560-001.sip.ld',
        '2345-12600-001.sip.ld',
        '2345-12670-001.sip.ld',
        '2345-17960-001.sip.ld',
        '3111-15600-001.sip.ld',
        '3111-30900-001.sip.ld',
        '3111-40000-001.sip.ld',
    ]

    polycom-provision::function::firmware { $firmwares: }

    $legacy_firmwares = [
        '2201-06642-001.sip.ld',
        '2345-11300-010.sip.ld',
        '2345-11500-030.sip.ld',
        '2345-11500-040.sip.ld',
        '2345-11600-001.sip.ld',
        '2345-11605-001.sip.ld',
    ]

    polycom-provision::function::firmware { $legacy_firmwares:
        legacy => 'yes',
    }

    apache::function::virtualhost { $polycom-provision::server::hostname:
        content     => template('polycom-provision/etc/apache2/conf.d/polycom-provision.conf.erb'),
    }

    apache::function::htdigest { $polycom-provision::server::hostname:
        authname    => 'polycom-provision',
        content     => template('polycom-provision/etc/apache2/conf.d/htdigest.conf.erb'),
        password    => $polycom-provision::server::password,
        username    => $polycom-provision::server::username,
    }

    $mods = [
        'dav',
        'dav_fs',
    ]

    apache::function::a2enmod { $mods: }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
