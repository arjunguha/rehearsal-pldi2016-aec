define kbp_riemann::client($riemann_tag="riemann_${customer}_${custenv}") {
  kbp_ferm::rule {
    'Riemann client tcp/udp':
      exported => true,
      saddr    => $ipaddress_eth1,
      proto    => '(tcp, udp)',
      dport    => 5555,
      action   => 'ACCEPT',
      ferm_tag => $riemann_tag;
    'Riemann client websockets':
      exported => true,
      saddr    => $ipaddress_eth1,
      proto    => 'tcp',
      dport    => 5556,
      action   => 'ACCEPT',
      ferm_tag => $riemann_tag;
  }
}

class kbp_riemann::server($riemann_tag="riemann_${customer}_${custenv}") {
  include gen_riemann::server

  file { '/etc/riemann/riemann.config':
    content => template('kbp_riemann/riemann.config'),
    owner   => 'riemann',
    group   => 'riemann',
    require => Package['riemann'];
  }

  Kbp_ferm::Rule <<| tag == $riemann_tag |>>
}
