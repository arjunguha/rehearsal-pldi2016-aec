class ntp::params {
  case $::lsbdistcodename {
    'squeeze': {
      $local  = hiera('local')
      $remote = hiera('remote')
    }
    default: {
      fail("Module ${module_name} does not support ${::lsbdistcodename}")
    }
  }
}
