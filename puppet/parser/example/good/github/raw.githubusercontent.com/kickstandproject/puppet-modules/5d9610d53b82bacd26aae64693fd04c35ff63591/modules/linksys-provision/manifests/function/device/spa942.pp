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
define linksys-provision::function::device::spa942(
    $label,
    $displayName,
    $password,
    $options = {},
) {
    require linksys-provision::server

    $base = "${linksys-provision::params::basedir}/configs"

    $split = split($name, '-')

    if ($split[1] != '') {
        $line = $split[1]
    } else {
        $line = '1'
    }

    $name_real = "${split[0]}"

    $defaults   = {
        'line'  => $line,
        'type'  => 'private',
    }

    $options_real = merge($defaults, $options)

    if (!$options_real['displayName']) {
        $options_real['displayName'] = $displayName
    }

    if (!$options_real['label']) {
        $options_real['label'] = $label
    }

    if (!$options_real['password']) {
        $options_real['password'] = $password
    }

    if (!defined(Common::Function::Concat["${base}/${name_real}.xml"])) {
        common::function::concat { "${base}/${name_real}.xml":
            require => File["${linksys-provision::params::basedir}/configs"],
        }

        common::function::concat::fragment { "${name_real}.xml-header":
            content => template('linksys-provision/var/lib/linksys-provision/configs/spa942.xml-header.erb'),
            order   => 01,
            target  => "${base}/${name_real}.xml",
        }

        common::function::concat::fragment { "${name_real}.xml-footer":
            content => template('linksys-provision/var/lib/linksys-provision/configs/spa942.xml-footer.erb'),
            order   => 03,
            target  => "${base}/${name_real}.xml",
        }
    }

    common::function::concat::fragment { "${name}.xml":
        content => template('linksys-provision/var/lib/linksys-provision/configs/spa942.xml.erb'),
        order   => 02,
        target  => "${base}/${name_real}.xml",
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
