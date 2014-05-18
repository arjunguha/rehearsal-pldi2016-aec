# Class: kbp_clamav
#
# Actions:
#  Set up ClamAV
#
# Depends:
#  gen_clamav
#  gen_puppet
#
class kbp_clamav {
  include gen_clamav

  user { 'clamav':
    require => Package['clamav-daemon','amavisd-new'],
    groups  => 'amavis';
  }
}
