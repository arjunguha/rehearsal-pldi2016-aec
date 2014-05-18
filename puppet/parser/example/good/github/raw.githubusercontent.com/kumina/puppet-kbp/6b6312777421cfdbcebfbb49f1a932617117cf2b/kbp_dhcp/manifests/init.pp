# Author: Kumina bv <support@kumina.nl>

# Class: kbp_dhcp::server
#
# Actions:
#  Install a DHCP server and open the firewall, configuring the server can only
#  be done by overriding the dhcpd.conf.. so try to use kbp_dhcp::server::config.
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_dhcp::server {
  include dhcp::server
  class { "kbp_icinga::dhcp":; }

  kbp_ferm::rule { "DHCP requests_v4":
    proto  => "udp",
    sport  => "bootpc",
    dport  => "bootps",
    action => "ACCEPT";
  }

  if $lsbdistcodename == 'wheezy' {
    Package <| title == 'isc-dhcp-common' |> {
      ensure => latest,
    }
  }
}

# Class: kbp_dhcp::server::common
#
# Actions:
#  Install a DHCP server and open the firewall, this class shouldn't be called directly.
#  Please use kbp_dhcp::server::subnet and kbp_dhcp::server::host
#
# Depends:
#  gen_dhcp::server
#  gen_puppet
#
class kbp_dhcp::server::common {
  include gen_dhcp::server
  class { "kbp_icinga::dhcp":; }

  kbp_ferm::rule { "DHCP requests_v4":
    proto  => "udp",
    sport  => "bootpc",
    dport  => "bootps",
    action => "ACCEPT";
  }

  if $lsbdistcodename == 'wheezy' {
    Package <| title == 'isc-dhcp-common' |> {
      ensure => latest,
    }
  }
}

# Class: kbp_dhcp::server::subnet
#
# Actions:
#  Configure a subnet for the DHCP server
#
# Parameters:
#  network_subnet:
#   The network-address of the subnet
#  network_netmask:
#   The netmask op the subnet
#  network_router:
#   The default gateway for the network
#  range:
#   An array with 2 elements, describing the range of addresses that the DHCP server hands out (or false for all)
#  name_servers:
#   and array with nameserver addresses pushed to the client
#  name_search:
#   An array with the seach domains for the clients
#  name_domain:
#   The domain for the clients
#
# Depends:
#  kbp_dhcp::server::common
#
define kbp_dhcp::server::subnet ($network_subnet, $network_netmask='255.255.255.0', $network_router, $range=false, $name_servers=['8.8.8.8','8.8.4.4'], $name_search=false, $name_domain=false, $ntp_servers=false, $next_server=false, $filename=false) {
  include kbp_dhcp::server::common
  gen_dhcp::server::subnet { $name:
    network_subnet  => $network_subnet,
    network_netmask => $network_netmask,
    network_router  => $network_router,
    range           => $range,
    name_servers    => $name_servers,
    name_search     => $name_search,
    name_domain     => $name_domain,
    ntp_servers     => $ntp_servers,
    next_server     => $next_server,
    filename        => $filename;
  }
}

# Class: kbp_dhcp::server::host
#
# Actions:
#  Configure a host with a 'static' IP for the DHCP server
#
# Parameters:
#  host_address:
#   The IP address for the host
#  host_macaddress:
#   The Mac-Address of the host
#  set_name:
#   Should we send the hostname as a DHCP option?
#
# Depends:
#  kbp_dhcp::server::common
#
define kbp_dhcp::server::host ($host_address, $host_macaddress, $set_name=false) {
  gen_dhcp::server::host { $name:
    host_address    => $host_address,
    host_macaddress => $host_macaddress,
    set_name        => $set_name;
  }
}
