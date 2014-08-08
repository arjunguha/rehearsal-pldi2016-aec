class backuppc::params {
  case $operatingsystem {
    'ubuntu', 'debian': {
      $package        = 'backuppc'
      $service        = 'backuppc'
      $topdir         = '/var/lib/backuppc'
      $config         = '/etc/backuppc/config.pl'
      $hosts          = '/etc/backuppc/hosts'
      $config_directory = '/etc/backuppc'
      $config_apache  = '/etc/apache2/conf.d/backuppc.conf'
    }
    default: {
      fail("Operating system ${operatingsystem} is not supported by this module")
    }
  }
}