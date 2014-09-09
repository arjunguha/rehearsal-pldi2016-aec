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
class asterisk::server::command {
    exec { 'asterisk-module-reload-ais.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-amd.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-asterisk.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-calendar.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-ccss.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-cdr_adaptive_odbc.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-cdr.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-cdr_custom.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-cdr_manager.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-cdr_syslog.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-cel.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-cel_custom.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-cel_odbc.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-cli.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-cli_permissions.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-codecs.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-dnsmgr.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-dsp.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-dundi.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-enum.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-extconfig.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-extensions.conf':
        command     => 'asterisk -rx "dialplan reload"',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-features.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-func_odbc.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-gtalk.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-http.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-iax.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-iaxprov.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-indications.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-jabber.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-logger.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-manager.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-meetme.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-modules.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-musiconhold.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-queuerules.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-queues.conf':
        command     => 'asterisk -rx "module reload app_queue.so"',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-res_curl.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-res_fax.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-res_ldap.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-res_odbc.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-res_stun_monitor.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-rtp.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-say.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-sip.conf':
        command     => 'asterisk -rx "module reload chan_sip.so"',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-sip_notify.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-smdi.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-udptl.conf':
        command     => 'true',
        refreshonly => true,
    }

    exec { 'asterisk-module-reload-voicemail.conf':
        command     => 'asterisk -rx "module reload app_voicemail.so"',
        refreshonly => true,
    }
}

# vim:sw=4:ts=4:expandtab:textwidth=79
