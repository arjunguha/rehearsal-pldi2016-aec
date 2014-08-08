# gvpe::node { "johnw.homeunix.net":
#   name => "johnw";
# }

class gvpe::node(
    $name
  , $port = 50000
  , $mtu = 1400
  , $ifname = "vpe0"
  , $network = "10.0.0.0/16")
{
  $etc = "/etc/gvpe"

  package { gvpe: ensure => latest }

  #
  # Create the if-up file
  #

  file { "$etc/if-up":
    owner   => root,
    mode    => 0700,
    ensure  => present,
    content => template("gvpe/if-up.erb"),
    require => Package[gvpe];
  }

  #
  # Create the gvpe.conf file, by assembling data collected from all nodes
  #

  @@file { "$etc/nodes.d/$name.conf":
    owner   => root,
    mode    => 0600,
    ensure  => present,
    content => template("gvpe/gvpe.conf.node.erb"),
    tag     => gvpe_node_conf;
  }

  file { "$etc/nodes.d":
    owner   => root,
    mode    => 0700,
    ensure  => directory,
    require => Package[gvpe];
  }

  file { "$etc/gvpe.conf.pre":
    owner   => root,
    mode    => 0600,
    ensure  => present,
    content => template("gvpe/gvpe.conf.pre.erb"),
    require => Package[gvpe];
  }

  exec { "assemble gvpe.conf for $title":
    command => "cat $etc/gvpe.conf.pre $etc/nodes.d/* > $etc/gvpe.conf",
    onlyif  => "expr `find $etc/nodes.d -newer $etc/gvpe.conf -type f -print | wc -l` \\> 0",
    require => [ File["$etc/nodes.d"], File["$etc/gvpe.conf.pre"] ];
  }

  File <<| tag == "gvpe_node_conf" |>> {
    notify => [ Exec["assemble gvpe.conf for $title"], Service[gvpe] ]
  }

  #
  # Create the node's private key
  #

  exec { "generate hostkey for $title":
    command => "openssl genrsa -out $etc/hostkey 1280",
    unless  => "test -f $etc/hostkey",
    require => Package[gvpe];
  }

  file { "$etc/hostkey":
    owner   => root,
    mode    => 0700,
    ensure  => present,
    require => Exec["generate hostkey for $title"];
  }

  #
  # Create the node's public key
  #

  exec { "generate pubkey for $title":
    command => "openssl rsa -in $etc/hostkey -pubout -out $etc/pubkey",
    unless  => "test -f $etc/pubkey",
    require => File["$etc/hostkey"];
  }

  file { "$etc/pubkey":
    owner   => root,
    mode    => 0700,
    ensure  => present,
    require => Exec["generate pubkey for $title"];
  }

  #
  # Distribute the node's public key to all other nodes
  #

  file { "$etc/pubkeys":
    owner   => root,
    mode    => 0700,
    ensure  => directory,
    require => Package[gvpe];
  }

  @@file { "$etc/pubkeys/$name":
    owner   => root,
    mode    => 0700,
    ensure  => present,
    source  => "$etc/pubkey",
    require => File["$etc/pubkey"],
    tag     => gvpe_node_pubkey;
  }

  File <<| tag == "gvpe_node_pubkey" |>> {
    notify  => Service[gvpe],
    require => File["$etc/pubkeys"]
  }

  #
  # Make sure the GVPE service is running.  This service gets refreshed every
  # time a new node's data is included in the .conf file and its public key is
  # received.
  #

  service { gvpe:
    ensure     => running,
    hasstatus  => true,
    hasrestart => true,
    enable     => true,
    require    => [ Exec["assemble gvpe.conf for $title"], File["$etc/if-up"] ];
  }
}
