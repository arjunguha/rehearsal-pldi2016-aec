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
define polycom-provision::function::firmware(
    $legacy = 'no',
) {
    include polycom-provision::params

    if ($legacy == 'no') {
        require polycom-ucs::client
        $target = $polycom-ucs::params::basedir
    } else {
        require polycom-ucs::legacy::client
        $target = $polycom-ucs::legacy::params::basedir
    }

    file { "${polycom-provision::params::basedir}/firmwares/${name}":
        ensure  => link,
        target  => "${target}/firmwares/${name}",
        require => File["${polycom-provision::params::basedir}/firmwares"],
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
