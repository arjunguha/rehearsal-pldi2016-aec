# Author: Kumina bv <support@kumina.nl>

# Class: kbp_rabbitmq
#
# Actions:
#  Setup a specific version of rabbitmq and deploy some config for it.
#
# Depends:
#  gen_rabbitmq
#  gen_puppet
#
class kbp_rabbitmq($rabbitmq_name=false, $port=5672, $ssl_cert=false, $ssl_key=false, $ssl_port=5671, $namespace='/', $aqmp=false, $stomp=false, $upstream_packages=true) {
  $real_class = $stomp ? {
    true  => "gen_rabbitmq::stomp",
    false => $aqmp ? {
      true  => "gen_rabbitmq::aqmp",
      false => "gen_rabbitmq",
    }
  }
  $real_tag = $rabbitmq_name ? {
    false   => "rabbitmq_${environment}",
    default => "rabbitmq_${rabbitmq_name}",
  }

  class {
    $real_class:
      ssl_cert          => $ssl_cert,
      ssl_key           => $ssl_key,
      ssl_port          => $ssl_port,
      upstream_packages => $upstream_packages;
    "kbp_icinga::rabbitmqctl":
      namespace         => $namespace;
  }

  Kbp_ferm::Rule <<| tag == $real_tag |>> {
    dport  => $ssl_cert ? {
      false   => $port,
      default => "(${port} ${ssl_port})",
    },
    proto  => "tcp",
    action => "ACCEPT",
  }
}

# Class: kbp_rabbitmq::client
#
# Actions:
#  Export the firewall rules we need so we can access the server.
#
# Depends:
#  gen_ferm
#  gen_puppet
#
define kbp_rabbitmq::client($saddr=$source_ipaddress) {
  kbp_ferm::rule { "Connections to RabbitMQ (${name})":
    saddr    => $saddr,
    tag      => "rabbitmq_${name}",
    exported => true;
  }
}
