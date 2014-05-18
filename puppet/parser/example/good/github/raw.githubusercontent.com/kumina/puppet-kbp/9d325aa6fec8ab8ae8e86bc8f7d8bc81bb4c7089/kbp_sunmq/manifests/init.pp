# Author: Kumina bv <support@kumina.nl>

# Class: kbp_sunmq
#
# Parameters:
#  withJMS
#    Undocumented
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_sunmq($withJMS=false) {
  kbp_ferm::rule { "SunMQ ports":
    proto  => "tcp",
    dport  => "(7676 10236)",
    action => "ACCEPT",
    tag    => "sunmq";
  }

  if $withJMS {
    kbp_ferm::rule { "SunMQ JMS port":
      proto  => "tcp",
      dport  => "10234",
      action => "ACCEPT",
      tag    => "sunmq";
    }
  }
}
