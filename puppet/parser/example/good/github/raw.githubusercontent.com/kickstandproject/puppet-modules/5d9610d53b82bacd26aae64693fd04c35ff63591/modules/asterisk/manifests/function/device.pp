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
define asterisk::function::device(
    $extension,
    $fullname,
    $secret,
    $callerid = '',
    $context = 'from-internal',
    $channel = 'SIP',
    $email = '',
    $host = 'dynamic',
    $mailbox = '',
    $queues = '',
    $template = '',
    $type = 'friend'
) {
    require asterisk::server

    $ast_type = $type
    $ast_template = $template
    $base = "${asterisk::params::basedir}/sip.conf.d/devices"
    $description = "${fullname} <${extension}>"
    if ($mailbox == '') {
        $mailbox_real = "${extension}@${context}"
    } else {
        $mailbox_real = $mailbox
    }
    $split = split($name, '-')

    if ($split[1] != '') {
        $line = $split[1]
    } else {
        $line = '1'
    }

    $filename = "${split[0]}-${line}"
    $md5secret = md5("${filename}:asterisk:${secret}")

    file { "$base/${filename}.conf":
        ensure  => present,
        content => template('asterisk/etc/asterisk/sip.conf.d/devices/template.conf.erb'),
        notify  => Exec['asterisk-module-reload-sip.conf'],
        require => File[$base],
    }

    exec { "asterisk-database-put-${filename}":
        command     => "asterisk -rx \"database put ${channel}/Device ${extension}@${context} ${filename}\"",
        refreshonly => true,
    }

    if ($mailbox != 'none') {
        asterisk::voicemail::function::mailbox { $mailbox_real:
            description => $description,
            email       => $email,
            fullname    => $fullname,
        }
    }

    if ($queues != '') {
        asterisk::function::queuemember { $filename:
            channel => $channel,
            queue   => $queues,
        }
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
