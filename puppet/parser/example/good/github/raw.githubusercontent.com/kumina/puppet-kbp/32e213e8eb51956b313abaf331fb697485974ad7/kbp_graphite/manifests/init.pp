class kbp_graphite($listen_ip='127.0.0.1', $graphite_tag = false) {
  include gen_graphite

  gen_apt::preference { 'graphite-carbon':
    repo => 'kumina-wheezy';
  }

  gen_apt::preference { 'python-django':; }

  file {
    '/etc/carbon/carbon.conf':
      content => template('kbp_graphite/carbon.conf'),
      require => Package['graphite-carbon'],
      notify  => Exec['reload-carbon-cache'];
    '/etc/default/graphite-carbon':
      content => template('kbp_graphite/graphite-carbon'),
      require => Package['graphite-carbon'];
  }

  $real_graphite_tag = $graphite_tag ? {
    false   => "graphite_${environment}_${custenv}",
    default => "graphite_${environment}_${custenv}_${graphite_tag}",
  }

  Kbp_ferm::Rule <<| tag == $real_graphite_tag |>> {
    daddr => $listen_ip,
  }
}

class kbp_graphite::client ($source_address=$ipaddress_eth1, $graphite_tag=false) {
  $real_graphite_tag = $graphite_tag ? {
    false   => "graphite_${environment}_${custenv}",
    default => "graphite_${environment}_${custenv}_${graphite_tag}",
  }

  kbp_ferm::rule { 'graphite access':
    exported => true,
    proto    => 'tcp',
    dport    => 2003,
    saddr    => $source_address,
    action   => 'ACCEPT',
    ferm_tag => $real_graphite_tag;
  }
}
