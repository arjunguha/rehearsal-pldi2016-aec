class backuppc::client (
    $full_period      = 6.97,
    $incr_period      = 0.97,
    $keep_full        = 1,
    $keep_incr        = 6,
    $maxage_full      = 90,
    $maxage_incr      = 30,
    $maxage_partial   = 3,
    $only             = undef,
    $exclude          = undef,
    $pinglimit        = 3,
    $blackoutcount    = 7,
    $xfer_method       = 'rsync',
    $xfer_loglevel     = 1
) inherits backuppc::client::params {
  user { 'backup':
    ensure  => present,
    shell   => '/bin/bash',
    comment => 'BackupPC',
    system  => true
  }

  package { 'rsync':
    ensure  => installed
  }

  file { "${home_directory}/backuppc.sh":
    ensure  => present,
    owner   => 'root',
    group   => 'root',
    mode    => '0755',
    source  => "puppet:///modules/${module_name}/client/backuppc.sh"
  }

  file { "${home_directory}/.ssh":
    ensure  => directory,
    mode    => 0700,
    owner   => 'backup',
    group   => 'backup',
  }
  

  @@concat { "${topdir}/pc/${::fqdn}/exclude.list":
    owner => 'backuppc',
    group => 'backuppc',
    mode  => 0750,
    tag   => "backuppc_exclude_${::domain}"
  }

  @@concat::fragment { "backuppc_host_${::fqdn}":
    target  => '/etc/backuppc/hosts',
    content => "${::fqdn} 0 backuppc\n",
    notify  => Service[$service],
    tag     => "backuppc_hosts_${::domain}"
  }
  
  @@file { "${topdir}/pc/${::fqdn}":
    ensure  => directory,
    owner   => 'backuppc',
    group   => 'backuppc',
    mode    => 0750,
    tag     => "backuppc_pc_${::domain}",
  }
  
  @@file { "${topdir}/pc/${::fqdn}/config.pl":
    ensure  => present,
    content => template("${module_name}/host.pl.erb"),
    owner   => 'backuppc',
    group   => 'www-data',
    mode    => '0740',
    notify  => Service[$service],
    tag     => "backuppc_config_${::domain}"
  }
  
  Ssh_authorized_key <<| tag == "backuppc_${::domain}" |>> {
    require => File["${home_directory}/.ssh"]
  }

  file { '/etc/sudoers.d/backup':
    ensure  => present,
    owner   => 'root',
    group   => 'root',
    mode    => 440,
    content => "backup ALL=(ALL:ALL) NOPASSWD: /usr/bin/rsync\n",
    require => Package['sudo']
  }
}