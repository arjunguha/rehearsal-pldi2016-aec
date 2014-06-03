# Author: Kumina bv <support@kumina.nl>

# This class is for system timekeeping with ntpd (or openntpd on lenny)
# Class: kbp_time
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_time {
  case $lsbdistcodename {
    'lenny' : {
      include openntpd::common
    }
    default : {
      include ntp
      include kbp_trending::ntpd
    }
  }
}
