# Author: Kumina bv <support@kumina.nl>

# Class: kbp_nsca::server
#
# Parameters:
#  package
#    Undocumented
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_nsca::server($package="icinga") {
  include gen_nsca::server

  if $package == "icinga" {
    File <| title == "/etc/nsca/nsca.cfg" |> {
      content => template("kbp_nsca/nsca.cfg_icinga"),
    }
  }

  Gen_ferm::Rule <<| tag == "nsca_${environment}" |>>
}

# Class: kbp_nsca::client
#
# Parameters:
#  package
#    Undocumented
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_nsca::client($package="munin") {
  include gen_nsca::client

  kbp_ferm::rule { "NSCA connections":
    saddr    => $source_ipaddress,
    proto    => "tcp",
    dport    => 5667,
    action   => "ACCEPT",
    exported => true,
    tag      => "nsca_${environment}";
  }
}
