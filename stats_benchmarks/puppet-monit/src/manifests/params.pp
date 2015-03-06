class monit::params {
  case $::lsbdistcodename {
    #(nimish) 'squeeze': {
    'trusty': {
    }
    default: {
      fail("Module ${module_name} does not support ${::lsbdistcodename}")
    }
  }
}
