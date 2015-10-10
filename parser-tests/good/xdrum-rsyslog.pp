# NOTE(arjun):
#
# Source: https://github.com/x-drum/puppet-rsyslog/commit/85ae95cdad982087e1d4100693e903e35ec23f2d

# NOTE(arjun): top-level edits
include rsyslog
$::osfamily = "linux"

# == Class: rsyslog
#
# A class for managing rsyslog server options
#
# Parameters:
# [*package_ensure*]
#    Ensure package installation [present, absent, purged, held, latest], default: present.
#
# [*default_config*]
#    Install a stanza with default configuration [true, false], default: false.
#
# Sample Usage:
# include 'rsyslog'
# class { 'rsyslog': 
#   package_ensure => absent,
#   default_config => true,
# }
#
# === Authors
#
# Alessio Cassibba (X-Drum) <swapon@gmail.com>
#
# === Copyright
#
# Copyright 2014 Alessio Cassibba (X-Drum), unless otherwise noted.
#
class rsyslog (
    $package_ensure = "present", # NOTE(arjun): quoted
    $default_config = false,
) { # NOTE(arjun): Inlined inherited variables inherits rsyslog::params {


  # NOTE(arjun): from the inherited class
  $config_file = '/etc/rsyslog.conf'
  $config_dir = '/etc/rsyslog.d'
  $package_name = 'rsyslog'
  $default_owner = "root"
  $default_group = "root"
  $service_name = 'rsyslog'



  package { $package_name:
    ensure => $package_ensure,
  }

  service { $service_name:
    ensure => 'running',
    enable => true,
    hasstatus => true,
    hasrestart => true,
    subscribe => [Package[$package_name], File[$config_file]], #NOTE(arjun): shortened FQ-name to config_file
    require => File[$config_file],
  }

  if $::osfamily == 'openbsd' and ! defined(File["/etc/rc.d/${service_name}"]) { # NOTE(arjun): shortened FQ-name to service_name
    file { "/etc/rc.d/${service_name}":
      ensure => present,
      owner => $default_owner,
      group => $default_group,
      mode => '0744',
      source => 'puppet:///modules/rsyslog/rsyslogd.rc',
      require => Package[$package_name],
    }
  }

  file { $config_file:
    ensure => present,
    owner => $default_owner,
    group => $default_group,
    mode => '0444',
    content => template("rsyslog/rsyslog.conf.erb"),
  }

  # note: all unmanaged config snippets will be discarded.
  file { $config_dir:
    ensure => 'directory',
    owner => $default_owner,
    group => $default_group,
    mode => '0755',
    recurse => true,
    purge => true,
    force => true,
  }

  if $default_config {
    rsyslog::snippet { '50-default':
      lines => [ '*.info;mail.none;authpriv.none;cron.none               /var/log/messages',
        'kern.*                      -/var/log/kern.log',
        'auth.*;authpriv.*           /var/log/auth.log',
        'daemon.*                    /var/log/daemon.log',
        'cron.*                      -/var/log/cron.log',
        'mail.*                      -/var/log/mail.log',
        'uucp,news.*                 /var/log/spooler',
        '*.emerg                     *',
        'local7.*                    /var/log/boot.log',
        '*.*                         /var/log/uncategorized.log',
      ]
    }
  }
}
# == Class: rsyslog::params
#
# part of rsyslog module, don't include directly
#
# === Authors
#
# Alessio Cassibba (X-Drum) <swapon@gmail.com>
#
# === Copyright
#
# Copyright 2014 Alessio Cassibba (X-Drum), unless otherwise noted.
#
#class rsyslog::params {
#	$config_file = '/etc/rsyslog.conf'
#	$config_dir = '/etc/rsyslog.d'
#	$package_name = 'rsyslog'
#
#	case $::osfamily {
#		openbsd: {
#			$default_owner = root
#			$default_group = wheel
#			$service_name = 'rsyslogd'
#		}
#		default: {
#			$default_owner = root
#			$default_group = root
#			$service_name = 'rsyslog'
#		}
#	}
#}
# == Class: rsyslog::snippet
#
# A resource for managing rsyslog client stanzas
#
# Parameters:
#  [*lines*]
#    An array containing stanza's lines.
#
# Sample Usage:
#  rsyslog::snippet { '20-puppet':
#    lines => [ ':programname, isequal, "puppet-agent" /var/log/puppet/puppet.log', '& ~' ],
#  }
#
#  will produce the file:
#  # HEADER: Warning: This file is managed by puppet,
#  # HEADER: *do not* edit manually.
#  :programname, isequal, "puppet-agent" /var/log/puppet/puppet.log
#  & ~
#
# === Authors
#
# Alessio Cassibba (X-Drum) <swapon@gmail.com>
#
# === Copyright
#
# Copyright 2014 Alessio Cassibba (X-Drum), unless otherwise noted.
#
define rsyslog::snippet (
  $lines
){
  include rsyslog

  if ! is_array($lines) {
    fail("The parameter lines must be an array.")
  }

  file { "$config_dir/${name}.conf":
    ensure => present,
    owner => $default_owner,
    group => $default_group,
    mode => '0444',
    content => template("rsyslog/snippet.conf.erb"),
    notify => Service[$service_name],
    require => File[$config_dir],
  }
}

