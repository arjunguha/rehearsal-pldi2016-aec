class apticron::params {
  case $::lsbdistcodename {
    'squeeze': {
      $apticron    = hiera('apticron')
      $listchanges = hiera('listchanges')
    }
    default: {
      fail("Module ${module_name} does not support ${::lsbdistcodename}")
    }
  }
}
