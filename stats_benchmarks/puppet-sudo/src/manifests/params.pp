class sudo::params {
  case $::lsbdistcodename {
    #(nimish) 'squeeze': {
    'trusty': {
      $admins  = "nimish" #(nimish) hiera('admin')
      $content = "some content" #(nimish) template("sudo/${::lsbdistcodename}/etc/sudoers.erb")
      $source  = undef
    }
    default: {
      fail("Module ${module_name} does not support ${::lsbdistcodename}")
    }
  }
}
