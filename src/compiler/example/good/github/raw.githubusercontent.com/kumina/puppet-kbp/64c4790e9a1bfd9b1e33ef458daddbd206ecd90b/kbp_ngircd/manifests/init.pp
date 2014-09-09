#
# Class: kbp_ngircd
#
# Actions: install ngircd and set up config
#
# Parameters:
#  servername: the name to display to clients
#  serverinfo: a hash containing one or more of the following fields: Info, AdminInfo1, AdminInfo2, AdminEMail (see the comments in the sample config for the meanings: http://ngircd.barton.de/doc/sample-ngircd.conf)
#  listen: array of IP addresses to bind to (false means: bind on everything)
#  ports: array of ports to bind to
#  motd: String with the full MOTD content
#  ssl_cert: the name of the ssl-cert/key (without .key/.pem)
#  ssl_dh_params: the Diffie-Hellman parameters for SSL
#  ssl_ports: array of ports to bind to for ssl
#
class kbp_ngircd ($servername=$fqdn, $serverinfo=false, $listen=[$ipaddress], $listen6=false, $ports=['6667'], $motd=false, $ssl_cert=false, $ssl_dh_params=false, $ssl_ports=false) {
  class { 'gen_ngircd':
    servername    => $servername,
    serverinfo    => $serverinfo,
    listen        => $listen,
    listen6       => $listen6,
    ports         => $ports,
    motd          => $motd,
    ssl_cert      => $ssl_cert,
    ssl_dh_params => $ssl_dh_params,
    ssl_ports     => $ssl_ports;
  }

  kbp_icinga::proc_status { 'ngircd':
    sms => false;
  }

  $the_ports = join($ports, ' ')

  $ips = join($listen, ' ')
  $ips6 = join($listen6, ' ')

  kbp_ferm::rule { 'IRC connections_v4':
    dport  => "(${the_ports})",
    daddr  => "(${ips})",
    proto  => 'tcp',
    action => 'ACCEPT';
  }

  if $listen6 {
    kbp_ferm::rule { 'IRC connections_v6':
      dport  => "(${the_ports})",
      daddr  => "(${ips6})",
      proto  => 'tcp',
      action => 'ACCEPT';
    }
  }


  if $ssl_ports {
    $the_ssl_ports = join($ssl_ports, ' ')
    kbp_ferm::rule { 'IRC connections (SSL)_v4':
      dport  => "(${the_ssl_ports})",
      daddr  => "(${ips})",
      proto  => 'tcp',
      action => 'ACCEPT';
    }
    if $listen6 {
      kbp_ferm::rule { 'IRC connections (SSL)_v6':
        dport  => "(${the_ssl_ports})",
        daddr  => "(${ips6})",
        proto  => 'tcp',
        action => 'ACCEPT';
      }
    }
  }
}
