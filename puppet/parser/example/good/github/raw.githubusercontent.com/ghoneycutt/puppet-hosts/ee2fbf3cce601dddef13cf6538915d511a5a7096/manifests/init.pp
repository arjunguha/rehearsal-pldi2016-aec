# Class: hosts
#
# This module manages /etc/hosts
#
# Requires:
#   class generic which provides $pop
#
class hosts {

    file { "/etc/hosts":
        ensure => present,
    } # file

    Host {
        ensure  => present,
        require => File["/etc/hosts"],
    } # Host

    # localhost
    host {
        "localhost":
            ip      => "127.0.0.1";
        # add /etc/hosts entry for the machine
        "$fqdn":
            ip     => $fqdn ? {
                default => "$ipaddress",
            },
            alias  => "$hostname.$pop";
    } # host
} # class hosts
