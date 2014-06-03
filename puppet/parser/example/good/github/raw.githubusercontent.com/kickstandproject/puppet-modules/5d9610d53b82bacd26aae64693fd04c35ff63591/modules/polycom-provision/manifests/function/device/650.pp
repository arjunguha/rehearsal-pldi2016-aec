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
define polycom-provision::function::device::650(
    $label,
    $displayName,
    $password,
    $options = {},
) {
    require polycom-provision::server

    $base = "${polycom-provision::params::basedir}/configs"

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

    if (!defined(Common::Function::Concat["${base}/${name_real}-user.cfg"])) {
        common::function::concat { "${base}/${name_real}-user.cfg":
            require => File["${polycom-provision::params::basedir}/configs"],
        }

        common::function::concat::fragment { "${name_real}-user.cfg-header":
            target  => "${base}/${name_real}-user.cfg",
            content => template('polycom-provision/var/lib/polycom-provision/configs/650.cfg-header.erb'),
            order   => 01,
        }

        common::function::concat::fragment { "${name_real}-user.cfg-footer":
            target  => "${base}/${name_real}-user.cfg",
            content => template('polycom-provision/var/lib/polycom-provision/configs/650.cfg-footer.erb'),
            order   => 03,
        }
    }

    common::function::concat::fragment { "${name}-user.cfg":
        target  => "${base}/${name_real}-user.cfg",
        content => template('polycom-provision/var/lib/polycom-provision/configs/650.cfg.erb'),
        order   => 02,
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
