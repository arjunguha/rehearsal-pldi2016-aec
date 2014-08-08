class ssh::params {
  case $::lsbdistcodename {
    'squeeze': {
      $group = hiera('group')
    }
    default: {
      fail("Module ${module_name} does not support ${::lsbdistcodename}")
    }
  }
}
