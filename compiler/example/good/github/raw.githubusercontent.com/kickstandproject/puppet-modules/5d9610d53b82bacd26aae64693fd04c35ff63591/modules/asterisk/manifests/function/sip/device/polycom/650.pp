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
define asterisk::function::sip::device::polycom::650(
    $extension,
    $fullname,
    $secret,
    $email  = '',
    $phone  = {},
    $sip    = {},
) {
    asterisk::function::sip::device { $name :
        extension   => $extension,
        fullname    => $fullname,
        secret      => $secret,
        email       => $email,
        options     => $sip,
    }

    polycom-provision::function::device::650 { $name :
        label       => $extension,
        displayName => $fullname,
        password    => $secret,
        options     => $phone,
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
