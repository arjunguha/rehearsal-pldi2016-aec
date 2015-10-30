# NOTES(arjun):
# This patch fixes the bug in this version:
#
# https://github.com/thias/puppet-bind/commit/2e693a457b147c2b0666d557cf3d5c45d71d913d

define bind::server::conf (
    #$acls               = {},
    #$masters            = {},
    $listen_on_port     = '53',
    $listen_on_addr     = [ '127.0.0.1' ],
    $listen_on_v6_port  = '53',
    $listen_on_v6_addr  = [ '::1' ],
    $forwarders         = [],
    $directory          = '/var/named',
    $version            = false,
    $dump_file          = '/var/named/data/cache_dump.db',
    $statistics_file    = '/var/named/data/named_stats.txt',
    $memstatistics_file = '/var/named/data/named_mem_stats.txt',
    $allow_query        = [ 'localhost' ],
    $allow_query_cache  = [],
    $recursion          = 'yes',
    $allow_recursion    = [],
    $dnssec_enable      = 'yes',
    $dnssec_validation  = 'yes',
    $dnssec_lookaside   = 'auto',
    #$zones              = {}
) {

    # Everything is inside a single template
    file { $title:
        notify => Service['named'],
        content => template('bind/named.conf.erb'),
    }

}

define bind::server::file (
    $zonedir = '/var/named',
    $owner   = 'root',
    $group   = 'named',
    $mode    = '0640',
    $source  = undef,
    $content = undef
) {

    file { "${zonedir}/${title}":
        owner   => $owner,
        group   => $group,
        mode    => $mode,
        source  => $source,
        content => $content,
        notify  => Service['named'],
    }

}


class bind::server (
    $chroot = true,
    # For RHEL5 you might want to use 'bind97'
    $bindpkgprefix = 'bind'
) {

    # Main package and service it provides
    $bindserverpkgname = "${bindpkgprefix}"

    package { $bindserverpkgname: ensure => installed }
    service { 'named':
        require   => Package[$bindserverpkgname],
        hasstatus => true,
        enable    => true,
        ensure    => running,
        restart   => '/sbin/service named reload',
    }

    # We want a nice log file which the package doesn't provide a location for
    $bindlogdir ='/var/log/named'

    file { $bindlogdir:
        require => Package[$bindserverpkgname],
        ensure  => directory,
        owner   => 'root',
        group   => 'named',
        mode    => '0770',
        seltype => 'named_log_t',
    }

}

# Taken from the "Sample Usage :"
include bind::server
bind::server::conf { '/etc/named.conf':
}

bind::server::file { 'example.com':
    #source => 'puppet:///modules/bind/named.empty',
}
