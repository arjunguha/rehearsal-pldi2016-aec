class backuppc::debian inherits backuppc::params {
  file { '/var/cache/debconf/backuppc.seeds':
    ensure  => present,
    source  => "puppet:///modules/${module_name}/debian/backuppc.preseed"
  }
}