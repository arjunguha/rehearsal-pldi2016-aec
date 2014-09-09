# Author: Kumina bv <support@kumina.nl>

# Class: kbp_proftpd
#
# Actions:
#  Setup ProFTPd the way we like it.
#
# Depends:
#  gen_proftpd
#  gen_puppet
#
class kbp_proftpd {
  include gen_proftpd

  kbp_ferm::rule { "Allow connections to FTP from everywhere.":
    proto  => "tcp",
    dport  => 21,
    action => "ACCEPT",
  }

  gen_linux::kmod { "nf_conntrack_ftp":
    ensure => present;
  }
}

# Class: kbp_proftpd::mysql
#
# Actions:
#  Setup MySQL authentication for ProFTPd.
#
# Depends:
#  kbp_proftpd
#  gen_puppet
#
class kbp_proftpd::mysql {
  include kbp_proftpd
  include gen_proftpd::mysql
}
