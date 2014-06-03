# Author: Kumina bv <support@kumina.nl>

# Class: kbp_asterisk::server
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_asterisk::server {
  include asterisk::server
  include kbp_icinga::asterisk

  gen_ferm::rule { "SIP connections":
    proto  => "udp",
    dport  => "(sip 15000:15100)",
    action => "ACCEPT";
  }

  @@gen_ferm::rule { "Asterisk CDR logging from ${fqdn}_v4":
    saddr  => $external_ipaddress,
    proto  => "tcp",
    dport  => 3306,
    action => "ACCEPT",
    tag    => "mysql_asterisk";
  }
}
