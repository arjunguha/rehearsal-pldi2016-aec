# Author: Kumina bv <support@kumina.nl>

# Class: kbp_bind
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_bind inherits bind {
  class { "kbp_trending::bind9":
    method => "munin"
  }

  gen_ferm::rule { "DNS connections":
    proto  => "(tcp udp)",
    dport  => 53,
    action => "ACCEPT";
  }

  kbp_ferm::rule { "Allow AXFR transfers":
    saddr    => $source_ipaddress,
    proto    => "(tcp udp)",
    dport    => 53,
    action   => "ACCEPT",
    exported => true,
    ferm_tag => "bind_${environment}";
  }
}
