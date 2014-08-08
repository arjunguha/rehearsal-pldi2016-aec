# Author: Kumina bv <support@kumina.nl>

# Class: kbp_openvpn::server
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_openvpn::server inherits openvpn::server {
  gen_munin::client::plugin { "openvpn":
    require => File["/etc/openvpn/openvpn-status.log"],
  }

  gen_munin::client::plugin::config { "openvpn":
    content => "user root\n",
  }

  # The Munin plugin has hardcoded the location of the status log, so we
  # need this symlink.
  file { "/etc/openvpn/openvpn-status.log":
    ensure  => link,
    target  => "/var/lib/openvpn/status.log",
    require => Package['openvpn'];
  }

  gen_ferm::rule { "OpenVPN connections":
    proto  => "udp",
    dport  => 1194,
    action => "ACCEPT";
  }

  gen_ferm::mod {
    "INVALID (forward)_v4":
      chain  => "FORWARD",
      mod    => "state",
      param  => "state",
      value  => "INVALID",
      action => "DROP";
    "ESTABLISHED RELATED (forward)_v4":
      chain  => "FORWARD",
      mod    => "state",
      param  => "state",
      value  => "(ESTABLISHED RELATED)",
      action => "ACCEPT";
  }
}

class kbp_openvpn::server_new ($ca_cert, $keylocation, $subnet, $subnet_mask, $dh_location, $push_gateway=false, $crl_location=false) {
  sysctl::setting { ['net.ipv4.conf.all.forwarding','net.ipv4.conf.default.forwarding']:
    value => '1';
  }
  kbp_ssl::keys { $keylocation:; }

  $certname = regsubst($keylocation,'^(.*)/(.*)$','\2')
  class { 'gen_openvpn::server':
    ca_cert      => $ca_cert,
    certname     => $certname,
    subnet       => $subnet,
    subnet_mask  => $subnet_mask,
    dh_location  => $dh_location,
    push_gateway => $push_gateway,
    crl_location => $crl_location,
    require      => [File["/etc/ssl/certs/${ca_cert}.pem"], Kbp_ssl::Keys[$keylocation]];
  }

  gen_munin::client::plugin { "openvpn":
    require => File["/etc/openvpn/openvpn-status.log"],
  }

  gen_munin::client::plugin::config { "openvpn":
    content => "user root\n",
  }

  # The Munin plugin has hardcoded the location of the status log, so we
  # need this symlink.
  file { "/etc/openvpn/openvpn-status.log":
    ensure  => link,
    target  => "/var/lib/openvpn/status.log",
    require => Package['openvpn'];
  }

  gen_ferm::rule { "OpenVPN connections":
    proto  => "udp",
    dport  => 1194,
    action => "ACCEPT";
  }

  gen_ferm::mod {
    "INVALID (forward)_v4":
      chain  => "FORWARD",
      mod    => "state",
      param  => "state",
      value  => "INVALID",
      action => "DROP";
    "ESTABLISHED RELATED (forward)_v4":
      chain  => "FORWARD",
      mod    => "state",
      param  => "state",
      value  => "(ESTABLISHED RELATED)",
      action => "ACCEPT";
  }
  gen_ferm::rule { "Traffic originating from OpenVPN_v4":
    chain     => "FORWARD",
    saddr     => "${subnet}/${subnet_mask}",
    interface => "tun+",
    action    => "ACCEPT";
  }
}

define kbp_openvpn::server_new::route ($network, $network_mask){
  gen_openvpn::server::route { $name:
    network      => $network,
    network_mask => $network_mask;
  }
}

define kbp_openvpn::client ($keylocation, $ca_cert, $remote_host=$name) {
  kbp_ssl::keys { $keylocation:; }

  $certname = regsubst($keylocation,'^(.*)/(.*)$','\2')
  gen_openvpn::client { $name:
    remote_host => $remote_host,
    ca_cert     => $ca_cert,
    certname    => $certname,
    require     => File["/etc/ssl/certs/${certname}.pem", "/etc/ssl/private/${certname}.key", "/etc/ssl/certs/${ca_cert}.pem"];
  }
}
