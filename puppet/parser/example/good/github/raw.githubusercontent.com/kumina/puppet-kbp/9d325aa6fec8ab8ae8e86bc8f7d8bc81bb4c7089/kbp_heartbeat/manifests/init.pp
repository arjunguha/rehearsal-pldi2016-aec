# Author: Kumina bv <support@kumina.nl>

# Class: kbp_heartbeat
#
# Parameters
#  autojoin
#    see man 5 ha.cf
#  warntime
#    see man 5 ha.cf
#  deadtime
#    see man 5 ha.cf
#  initdead
#    see man 5 ha.cf
#  keepalive
#    see man 5 ha.cf
#  crm
#    see man 5 ha.cf
#  node_name
#    The name of the node(this is used to build the node directives in ha.cf)
#  node_dev
#    The device used for heartbeat communication
#  node_ip
#    The IP used by the node communicate
#  customtag
#    Used when exporting and importing the configuration options. Change this when you have more than 1 heartbeat cluster.
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_heartbeat($autojoin="none", $warntime=5, $deadtime=15, $initdead=60, $keepalive=2, $crm="respawn", $node_name=$hostname, $node_dev="eth0", $node_ip=$ipaddress_eth0, $heartbeat_tag="${environment}_${custenv}") {
  $real_heartbeat_tag = "heartbeat_${heartbeat_tag}"

  include kbp_icinga::heartbeat
  class { "gen_heartbeat":
    autojoin      => $autojoin,
    warntime      => $warntime,
    deadtime      => $deadtime,
    initdead      => $initdead,
    keepalive     => $keepalive,
    crm           => $crm,
    node_name     => $node_name,
    node_ip       => $node_ip,
    node_dev      => $node_dev,
    heartbeat_tag => $real_heartbeat_tag;
  }

  Kbp_ferm::Rule <<| tag == $real_heartbeat_tag |>>

  kbp_ferm::rule { "Heartbeat connections":
    exported => true,
    saddr    => $node_ip,
    proto    => "udp",
    dport    => 694,
    action   => "ACCEPT",
    ferm_tag => $real_heartbeat_tag;
  }
}
