# Author: Kumina bv <support@kumina.nl>

# Class: kbp_p910nd::server
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_p910nd::server {
  include p910nd::server

  kbp_ferm::rule { "Printing connections":
    proto     => "tcp",
    dport     => "9100",
    action    => "ACCEPT";
  }
}
