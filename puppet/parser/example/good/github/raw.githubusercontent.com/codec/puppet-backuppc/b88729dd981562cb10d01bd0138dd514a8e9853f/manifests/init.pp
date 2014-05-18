# Class: backuppc
#
# This module manages backuppc
#
# Parameters:
#
# Actions:
#
# Requires:
#
# Sample Usage:
#
# [Remember: No empty lines between comments and class definition]
class backuppc inherits backuppc::params {
  include concat::setup
  
  # Set up dependencies
  Package[$package] -> File[$config] -> Service[$service]

  # Include preseeding for debian packages
  case $operatingsystem {
    'ubuntu', 'debian': {
      include backuppc::debian
    }
  }

  # BackupPC package and service configuration
  package { $package:
    ensure  => installed,
  }

  service { $service:
    ensure    => running,
    hasstatus => false,
    pattern   => 'BackupPC'
  }

  file { $config:
    ensure  => present,
    owner   => 'backuppc',
    group   => 'www-data',
    mode    => '0644',
    # content => template("${module_name}/config.pl"),
  }
  
  file { $config_directory:
    ensure  => present,
    owner   => 'backuppc',
    group   => 'www-data',
    require => Package[$package]
  }
  
  exec { 'backuppc-ssh-keygen':
    command => "/usr/bin/ssh-keygen -f ${topdir}/.ssh/id_rsa -C 'BackupPC on ${::fqdn}' -N ''",
    user    => 'backuppc',
    unless  => "test -f ${topdir}/.ssh/id_rsa"
  }

  # Export backuppc's authorized key to all clients
  @@ssh_authorized_key { "backuppc_${::fqdn}":
    ensure  => present,
    key     => $::backuppc_pubkey_rsa,
    name    => "backuppc_${::fqdn}",
    user    => 'backup',
    options => [
      "from=\"${::ipaddress}\"",
      'command="/var/backups/backuppc.sh"'
    ],
    type    => 'ssh-rsa',
    tag     => "backuppc_${::domain}",
  }
  
  # Hosts
  concat { '/etc/backuppc/hosts':
    owner => 'backuppc',
    group => 'backuppc',
    mode  => 0750
  }
  
  # FIXME: we use a custom fact to setup concat ...
  create_resources('concat', $backuppc_hosts, {
    owner => 'backuppc',
    group => 'backuppc',
    mode  => 0750
  })

  concat::fragment { 'hosts_header':
    target  => '/etc/backuppc/hosts',
    content => "host        dhcp    user    moreUsers     # <--- do not edit this line\n",
    order   => 01,
  }
  
  File <<| tag == "backuppc_pc_${::domain}" |>>
  File <<| tag == "backuppc_config_${::domain}" |>>
  Concat::Fragment <<| tag == "backuppc_hosts_${::domain}" |>>

  Concat <<| tag == "backuppc_exclude_${::domain}" |>>
  Concat::Fragment <<| tag == "backuppc_exclude_${::domain}" |>>
}
