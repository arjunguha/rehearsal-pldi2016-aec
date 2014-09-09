class common::params {
  case $::lsbdistcodename {
    'squeeze': {
    }
    default: {
      fail("Module ${module_name} does not support ${::lsbdistcodename}")
    }
  }
}
