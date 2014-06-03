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
define polycom-provision::function::legacy::site(
    $content = '',
) {
    require polycom-provision::server

    if ($content == '') {
        $content_real = template('polycom-provision/var/lib/polycom-provision/legacy/site.cfg.erb')
    } else {
        $content_real = $content
    }

    file { "${polycom-provision::params::basedir}/legacy/site.cfg":
        ensure  => present,
        content => $content_real,
        require => File["${polycom-provision::params::basedir}/legacy"],
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
