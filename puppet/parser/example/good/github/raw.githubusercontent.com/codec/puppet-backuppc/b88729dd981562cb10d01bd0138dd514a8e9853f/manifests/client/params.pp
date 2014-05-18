class backuppc::client::params inherits backuppc::params {
  case $operatingsystem {
    'ubuntu', 'debian': {
      $home_directory = '/var/backups'
    }
    default: {
      fail("Operating system ${operatingsystem} is not supported by this module")
    }
  }
}