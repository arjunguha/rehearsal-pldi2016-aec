#
# Class: kbp_elasticsearch
#
# Actions: Set up elasticsearch and configure it. Import client firewall rules
#
# Parameters:
#  cluster_name: The name of the cluster
#  bind_address: The IP address to bind on
#  node_name: The name of the node in the cluster
#  path_data: The path to the elasticsearch data
#  elasticsearch_tag: The tag for this instance
#
# Depends:
#  gen_elasticsearch
#
class kbp_elasticsearch ($min_nodes, $cluster_name='elasticsearch', $path_data='/srv/elasticsearch', $extra_opts=false, $heapsize=false, $elasticsearch_tag=false, $nodes=false, $overwrite_config=true){
  include kbp_icinga::elasticsearch

  class { 'gen_elasticsearch':
    cluster_name     => $cluster_name,
    path_data        => $path_data,
    min_nodes        => $min_nodes,
    nodes            => $nodes,
    extra_opts       => $extra_opts,
    overwrite_config => $overwrite_config,
    heapsize         => $heapsize;
  }

  # We want to find new nodes immidiately
  gen_ferm::mod {
    'Elasticsearch Multicast Discovery_v4':
      mod    => 'pkttype',
      param  => 'pkt-type',
      # H4cks :)
      value  => 'multicast daddr 224.2.2.4 proto udp dport 54328',
      action => 'ACCEPT';
  }

  $elasticsearch_ferm_tag = $elasticsearch_tag ? {
    false   => "${environment}_${dcenv}_elasticsearch",
    default => "${environment}_${dcenv}_elasticsearch_${elasticsearch_tag}",
  }

  Kbp_ferm::Rule <<| tag == $elasticsearch_ferm_tag |>>
}

#
# Class: kbp_elasticsearch::client
#
# Actions: Export some settings for the elasticsearch firewall
#
# Parameters:
#  saddr: The address the client will be connecting from
#  elasticsearch_tag: The tag for this instance
#
# Depends:
#  kbp_ferm
#
class kbp_elasticsearch::client ($saddr, $elasticsearch_tag=false) {
  $elasticsearch_ferm_tag = $elasticsearch_tag ? {
    false   => "${environment}_${dcenv}_elasticsearch",
    default => "${environment}_${dcenv}_elasticsearch_${elasticsearch_tag}",
  }

  kbp_ferm::rule { 'Elasticsearch access':
    saddr    => $saddr,
    proto    => 'tcp',
    dport    => '9200:9399',
    action   => 'ACCEPT',
    exported => true,
    ferm_tag => $elasticsearch_ferm_tag;
  }
}

#
# Class: kbp_elasticsearch::plugin
#
# Actions: Install a plugin for elasticsearch
#
# Parameters:
#  name: The 'path' to the plugin (used to call plugin) (e.g. mobz/elasticsearch-head for the head plugin)
#  install_name: The name the plugin will have on-disk
#
# Depends:
#  gen_elasticsearch
#
define kbp_elasticsearch::plugin ($install_name) {
  gen_elasticsearch::plugin { $name:
    install_name => $install_name;
  }
}
