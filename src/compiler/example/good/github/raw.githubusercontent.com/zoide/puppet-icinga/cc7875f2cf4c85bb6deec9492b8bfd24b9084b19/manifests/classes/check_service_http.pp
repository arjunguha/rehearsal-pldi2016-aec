# $Id$
class icinga::check::http::all ($ensure = "present") {
    class {
        ["icinga::check::http", "icinga::check::https"] :
            ensure => $ensure,
    }
}
define icinga::check::http_expect ($ensure = "present",
    $expect,
    $ssl = "false") {
    $s = $ssl ? {
        "true" => "s",
    }
    icinga::service {
        "${fqdn}_${name}" :
            service_description => "${name}",
            check_command => "check_http${s}_expect!${expect}",
            ensure => $ensure,
    }
    $cmd_real =
    "/usr/lib/nagios/plugins/check_http -H '\$HOSTNAME\$' -e \$ARG1"
    if !defined(Icinga::Command["check_https_expect"]) {
        icinga::command {
            "check_https_expect" :
                command_line => "${cmd_real} --ssl"
        }
    }
    if !defined(Icinga::Command["check_http_expect"]) {
        icinga::command {
            "check_http_expect" :
                command_line => "${cmd_real}"
        }
    }
}
class icinga::check::http ($ensure = "present") {
    Icinga::Service {
        ensure => $ensure
    }
    icinga::service {
        "${fqdn}_http" :
            service_description => "HTTP",
            check_command => "check_http!${fqdn}!${ipaddress}",
    }
}
class icinga::check::https ($ensure = "present") {
    Icinga::Service {
        ensure => $ensure
    }
    $fqdn_real = downcase($fqdn)
    icinga::service {
        "${fqdn}_https" :
            service_description => "HTTPS",
            check_command => "check_https!${fqdn_real}!${ipaddress}",
    }
}
class icinga::check::http_tcp ($ensure = "present") {
    Icinga::Service {
        ensure => $ensure
    }
    icinga::service {
        "${fqdn}_http_tcp" :
            service_description => "HTTPTCP",
            check_command => "check_tcp!80",
    }
}
class icinga::check::http_tcp::all ($ensure = "present") {
    Icinga::Service {
        ensure => $ensure
    }
    icinga::service {
        "${fqdn}_http_tcp" :
            service_description => "HTTPTCP",
            check_command => "check_tcp!80",
    }
    icinga::service {
        "${fqdn}_https_tcp" :
            service_description => "HTTPSTCP",
            check_command => "check_tcp!443",
    }
}
