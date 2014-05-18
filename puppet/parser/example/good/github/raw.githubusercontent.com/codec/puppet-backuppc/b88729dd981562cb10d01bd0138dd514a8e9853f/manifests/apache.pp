class backuppc::apache inherits backuppc::params {
  file { $config_apache:
    ensure  => symlink,
    target  => '/etc/backuppc/apache.conf',
    require => Package[$package]
  }
}