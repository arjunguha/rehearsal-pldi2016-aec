# Author: Kumina bv <support@kumina.nl>

# Class: kbp_ferm
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_ferm {
  include kbp_ferm::offenders
  include gen_ferm

  # Basic rules
  gen_ferm::rule {
    "Respond to ICMP packets_v4":
      proto    => "icmp",
      icmptype => "echo-request",
      action   => "ACCEPT";
    "Drop UDP packets":
      prio  => "a0",
      proto => "udp";
    "Nicely reject tcp packets":
      prio   => "a1",
      proto  => "tcp",
      action => "REJECT reject-with tcp-reset";
    "Reject everything else":
      prio   => "a2",
      action => "REJECT";
    "Drop UDP packets (forward)":
      prio  => "a0",
      proto => "udp",
      chain => "FORWARD";
    "Nicely reject tcp packets (forward)":
      prio   => "a1",
      proto  => "tcp",
      action => "REJECT reject-with tcp-reset",
      chain  => "FORWARD";
    "Reject everything else (forward)":
      prio   => "a2",
      action => "REJECT",
      chain  => "FORWARD";
    "Respond to ICMP packets (NDP)_v6":
      prio     => 00001,
      proto    => "icmpv6",
      icmptype => "(neighbour-solicitation neighbour-advertisement)",
      action   => "ACCEPT";
    "Respond to ICMP packets (diagnostic)_v6":
      proto    => "icmpv6",
      icmptype => "echo-request",
      action   => "ACCEPT";
  }

  include kbp_icinga::emptyfirewall
  class { "kbp_icinga::ferm_config":
    filename => "/etc/ferm/ferm.conf";
  }
}

# Class: kbp_ferm::offenders
#
# Parameters:
#  None
#
# Actions:
#  Disable access from known bad IP addresses to all machines in our control.
#  Use with care.
#
# Depends:
#  kbp_ferm
#  gen_puppet
#
class kbp_ferm::offenders {
  # Please add a comment describing when the IP was added and what for.
  kbp_ferm::block {
    "20130212 Ssh brute force attacks":
      ips => "(180.210.207.249 122.225.107.98 149.3.129.77 211.154.213.122 63.137.151.25)";
    "20130302 Attackers on EY":
      ips => "(188.143.233.2 193.169.124.50 94.153.105.252)";
    "20130316 SASL attackers":
      ips => "(218.201.74.57 116.213.94.19 95.240.32.27 93.57.70.125 89.97.206.218 89.119.220.57 74.95.89.172 71.43.34.10 71.12.111.186 70.62.15.91 60.231.152.189)";
    "20130316 More SASL attackers":
      ips => "(212.91.92.30 201.142.112.226 195.89.38.162 194.73.231.83 188.216.27.224 188.203.150.206 178.23.215.191 151.73.202.102 151.12.152.26)";
    "20130316 Even more SASL attackers":
      ips => "(65.9.239.119 95.241.170.2)";
    "20130316 Abusers of Wordpress send-to-a-friend script":
      ips => '(41.203.67.55 41.203.67.53 114.79.49.91 41.71.136.167 41.71.153.106 41.71.159.123)';
    "20130517 Brute forcers":
      ips => '(151.84.95.177 209.159.40.34 24.227.47.42 50.196.225.5 63.252.106.18 70.107.235.56 70.59.223.28 74.7.177.82 80.174.199.44 83.70.206.249 41.161.72.74)';
    "20130524 Attack on Wordpress sites":
      ips => '188.138.33.41';
    "20130703 Another attack on Wordpress sites":
      ips => '188.165.230.24';
    "20130729 Yet another attack on Wordpress sites":
      ips => '(192.198.86.230 192.111.153.142 192.111.151.34 199.180.119.18 54.227.242.219 178.132.203.37 46.119.114.120 94.76.77.146 89.248.61.60 91.206.206.26)';
    "20130731 SASL brute force attack":
      ips => '88.255.125.226';
    "20130803 Attack on Wordpress sites":
      ips => '(188.138.33.149 94.102.56.219)';
    '20130815 SSH brute force attack':
      ips => '(219.235.126.174 118.244.14.49 89.167.22.226 189.50.11.114 37.247.102.178 58.240.17.250 124.160.194.27 50.23.112.226 61.55.135.183 166.78.132.130 5.135.187.40 123.49.35.203)';
    '20130816 SSH brute force attack':
      ips => '(223.4.31.14 200.26.191.123 113.128.251.21 202.165.179.171)';
    '20130816 Wordpress attack':
      ips => '(59.163.249.182 50.122.120.108)';
    '20130817 SSH brute force attack':
      ips => '(80.87.78.4 195.19.173.244 211.100.49.165 61.16.234.205 108.171.184.25 218.1.71.151 61.16.234.205 211.142.247.90 153.19.91.74 70.104.144.29 190.120.230.192 219.146.225.147 89.255.22.170)';
    '20130821 Persistent SSH brute forcers':
      ips => '(113.107.88.29 218.108.250.205 60.191.47.13 67.205.111.20 118.186.210.98)';
    '20130822 Persistent SSH brute forcer':
      ips => '210.51.10.158';
    '20130826 Sneak ssh brute forcer':
      ips => '91.212.177.6';
    '20130917 DoS-er':
      ips => '(5.39.69.25 192.187.118.157 60.168.16.90 192.187.116.237 91.236.74.121 60.168.19.253 176.31.235.120)';
    '20130926 Persistent SASL/IMAP attacker':
      ips => '64.199.111.26';
    '20130928 Subnet that seems to be ssh brute forcing from all IPs':
      ips => '222.52.118.0/24';
    '20131008 Persistent attacker':
      ips => '202.123.180.82';
    '20131016 Wordpress attacker':
      ips => '(89.248.172.121 199.101.184.182)';
    '20131027 Asterisk brute-forcer':
      ips => '178.162.199.9';
    '20131103 Persistent brute forcer':
      ips => '115.114.14.195';
    '20131117 SASL brute forcer':
      ips => '123.209.136.24';
    '20131122 SSH brute forcers':
      ips => '(121.197.10.247 121.197.10.247)';
    '20131125 Sasl brute forcer and trying to see if smtp is an open relay':
      ips => '58.250.119.237';
    '20131127 SSH brute forcer':
      ips => '(60.249.201.106 212.83.150.15)';
    '20131208 Sasl attackers':
      ips => '(84.183.52.200 212.67.215.178 79.148.247.154 87.139.213.236 95.17.250.169 96.56.180.218 115.182.62.208)';
    '20131209 More SASL attackers':
      ips => '(212.36.65.106 50.194.97.85 63.117.127.109 96.10.209.82)';
    '20131216 Sasl attacker':
      ips => '70.89.83.193';
    '20131216 SSH dosser':
      ips => '222.175.114.134';
    '20131218 Postfix attacker':
      ips => '1.163.157.44';
    '20131220 SASL attackers':
      ips => '(12.165.233.2 12.236.34.135 148.245.17.19 188.80.255.199 188.85.195.111 201.203.113.66 212.174.252.130 74.93.146.17 76.5.225.8 79.136.209.193)';
    '20131222 Wordpress Attackers':
      ips => '(204.93.208.219 173.254.28.14)';
    '20131225 SASL attackers':
      ips => '(189.47.132.239 201.204.238.62 203.129.196.26 50.195.96.197 50.242.146.129 63.115.40.56 68.106.154.166 75.176.164.191 76.109.95.86 77.231.181.146 87.224.78.133 96.234.38.2)';
    '20131227 Various returning attackers':
      ips => '(61.182.170.38 218.205.178.51 218.25.54.25 200.160.125.17 119.188.3.56)';
    '20131231 SSH bruteforcer':
      ips => '107.6.3.235';
    '20140105 Attackers':
      ips => '(124.115.18.15 202.85.221.153 89.248.172.58)';
    '20140110 SSH brute forcers':
      ips => '(83.229.14.130 93.174.93.51)';
    '20140113 SSH brute forcers':
      ips => '(221.131.116.21 200.77.249.162 212.71.233.162 31.11.90.142 1.234.47.57)';
    '20140116 SSH brute forcers':
      ips => '(117.79.91.73 175.99.95.240 153.122.29.97 202.108.133.233 115.236.81.248 77.40.50.146)';
    '20140121 SSH brute forcers':
      ips => '(96.44.154.122 36.39.246.121 182.74.57.85 194.143.136.237)';
    '20140130 SSH brute forcers':
      ips => '(69.163.37.34 190.81.85.87 182.131.21.89 61.142.106.34 199.71.214.66 58.215.56.110 219.239.34.202 93.174.95.82 199.71.214.66 201.130.171.132)';
    '20140131 SSH brute forcers':
      ips => '(178.18.27.34 103.5.126.201)';
    '20140204 SASL attackers':
      ips => '(74.208.9.216 74.208.72.28 74.208.72.72)';
    '20140204 SSH attackers':
      ips => '(162.209.53.127 88.150.186.179 123.129.216.39 222.186.128.22 123.242.184.87 61.136.171.198 212.85.158.124 82.213.48.69 77.46.136.60 219.92.48.42 218.203.108.129 37.187.24.215 111.1.1.67 125.65.245.146)';
    '20140206 SASL attackers':
      ips => '(192.208.186.2 217.160.226.122)';
    '20140206 Repeated SSH attacker':
      ips => '212.104.149.56';
    '20140207 DoS attacker':
      ips => '5.135.135.42';
  }

  kbp_ferm::spammer {
    "20130122 Spammer":
      ips => '77.241.91.53';
    "20130124 A company dedicated to spamming":
      ips => '78.41.64.0/27';
    "20130403 Known spammer (ymlp)":
      ips => '85.158.212.97';
    '20130419 Logo design spammer':
      ips => '178.33.17.1';
    '20130419 "I r a 25 yo God fearing..." spammer':
      ips => '163.20.145.21';
    '20130531 Company dedicated to spamming (verkoop.nl)':
      ips => '194.120.161.149';
    '20130603 Restaurant spammer':
      ips => '(217.148.80.232 217.115.203.217)';
    '20130627 Phisher':
      ips => '83.168.246.219';
    '20130722 Company dedicated to spamming':
      ips => '87.237.8.204';
    '20130806 Restaurant spammer':
      ips => '217.148.80.238';
    '20130908 Non-opt-in mailinglist spam':
      ips => '195.140.184.0/22';
    '20131002 Restaurant spammer':
      ips => '208.117.55.143';
    '20131101 Profesional spammers':
      ips => '(46.17.4.184 200.35.148.94)';
    '20131107 ymlp again':
      ips => '87.237.8.203';
    '20140110 Company dedicated to spamming':
      ips => '78.128.76.47';
    '20140110 Restaurant spammer':
      ips => '77.245.88.181';
  }

  if ! defined(Concat['/etc/ferm/attackers.conf']) {
    concat { '/etc/ferm/attackers.conf':
      notify  => Exec['reload-ferm'],
      require => Package['ferm'],
      group   => 'adm';
    }

    concat::add_content {
      'v4_filter_INPUT_050_include_attackers':
        target  => '/etc/ferm/ferm.conf',
        content => "\t\t@include 'attackers.conf';\n",
        require => Gen_ferm::Chain['INPUT_filter_v4'];
      'v4_filter_FORWARD_050_include_attackers':
        target  => '/etc/ferm/ferm.conf',
        content => "\t\t@include 'attackers.conf';\n",
        require => Gen_ferm::Chain['FORWARD_filter_v4'];
    }
  }
}

# Define: kbp_ferm::block
#
# Parameters:
#  name
#    Description of why these IP addresses are blocked
#  ips
#    Comma-separated list of IP addresses to block
#
# Actions:
#  Drops all traffic from the IP address.
#
# Depends:
#  kbp_ferm
#  gen_puppet
#
define kbp_ferm::block ($ips) {
  concat::add_content { "${name}":
    target  => '/etc/ferm/attackers.conf',
    content => "# ${name}\nsaddr ${ips} DROP;";
  }
}

# Define: kbp_ferm::spammer
#
# Parameters:
#  name
#    Description of why these IP addresses are spammers, add a date added please
#  ips
#    List of IP addresses to block email from in ferm syntax
#
# Actions:
#  Drops all mail traffic from the IP address.
#
# Depends:
#  kbp_ferm
#  gen_puppet
#
define kbp_ferm::spammer ($ips) {
  concat::add_content { "Spam: ${name}":
    target  => '/etc/ferm/attackers.conf',
    content => "# SPAM: ${name}\nsaddr ${ips} proto tcp dport (25 465) DROP;";
  }
}

# Define: kbp_ferm::forward
#
# Parameters:
#  proto
#    The protocol that should be forwarded (usually tcp, so it defaults to that)
#  listen_addr
#    The address to listen on
#  listen_port
#    The port to listen on
#  dest_addr
#    The destination address
#  dest_port
#    The destination port (on the machine that uses the destination address), defaults to
#    listen_port.
#
#  TODO inc, port, dest, dport are legacy and should be replaced.
#
# Actions:
#  Setup a forward on a specific port to another ip address and optionally another port.
#
# Depends:
#  gen_ferm
#  gen_puppet
#
# TODO:
#  Once every setup uses the new invocation, the definition header can change into:
#define kbp_ferm::forward($listen_addr, $listen_port, $dest_addr, $dest_port = false, $proto = "tcp") {
define kbp_ferm::forward($listen_addr = false, $listen_port = false, $dest_addr = false, $dest_port = false, $proto = "tcp",
                         $inc = false, $port = false, $dest = false, $dport = false) {
  # Warn about legacy
  if $inc or $port or $dest or $dport {
    notify { "The definition of kbp_ferm::forward has changed. Please update the code for this host to use the new definition! Resource: kbp_ferm::forward { ${name}:; }":; }
  }

  # Most of the following checks can be removed once the definition has changed, except for
  # the $dest_port, because that should be $listen_port if not set. TODO
  if ! $dest_port {
    if $dport { $r_dest_port = $dport       }
    else      { $r_dest_port = $listen_port }
  } else {
    $r_dest_port = $dest_port
  }

  if ! $dest_addr {
    if $dest { $r_dest_addr = $dest         }
    else     { fail('No $dest_addr given.') }
  } else {
    $r_dest_addr = $dest_addr
  }

  if ! $listen_port {
    if $port { $r_listen_port = $port         }
    else     { fail('No $listen_port given.') }
  } else {
    $r_listen_port = $listen_port
  }

  if ! $listen_addr {
    if $inc { $r_listen_addr = $inc          }
    else    { fail('No $listen_addr given.') }
  } else {
    $r_listen_addr = $listen_addr
  }

  # TODO If you remove the $r_* vars above, don't forget to change them here!
  gen_ferm::rule {
    "Accept all ${proto} traffic from ${r_listen_addr}:${r_listen_port} to ${r_dest_addr}:${r_dest_port}_v4":
      chain     => "FORWARD",
      daddr     => $r_dest_addr,
      proto     => $proto,
      dport     => $r_dest_port,
      action    => "ACCEPT";
    "Forward all ${proto} traffic from ${r_listen_addr}:${r_listen_port} to ${r_dest_addr}:${r_dest_port}_v4":
      table     => "nat",
      chain     => "PREROUTING",
      daddr     => $r_listen_addr,
      proto     => $proto,
      dport     => $r_listen_port,
      action    => "DNAT to \"${r_dest_addr}:${r_dest_port}\"";
  }
}

define kbp_ferm::rule($prio=500, $interface=false, $outerface=false, $saddr=false, $daddr=false, $proto=false,
    $icmptype=false, $sport=false, $dport=false, $jump=false, $action=DROP, $table=filter,
    $chain=INPUT, $ensure=present, $exported=false, $ferm_tag=false, $fqdn=$fqdn, $ipaddress6=$ipaddress6, $customtag="foobar") {
    if $customtag != "foobar" { notify { "kbp_ferm::rule ${name} customtag: ${customtag}":; } }
  if ! $exported {
    gen_ferm::rule { $name:
      prio       => $prio,
      interface  => $interface,
      outerface  => $outerface,
      saddr      => $saddr,
      daddr      => $daddr,
      proto      => $proto,
      icmptype   => $icmptype,
      sport      => $sport,
      dport      => $dport,
      jump       => $jump,
      action     => $action,
      table      => $table,
      chain      => $chain,
      ensure     => $ensure,
      fqdn       => $fqdn,
      ipaddress6 => $ipaddress6;
    }
  } else {
    if ! $saddr and ! $daddr {
      fail("Exported ferm rule ${name} has no \$saddr and no \$daddr")
    }
    if $saddr and $daddr {
      $real_name = "${name} (exported by ${fqdn})"
    } elsif $saddr {
      $real_name = "${name} from ${fqdn}"
    } else {
      $real_name = "${name} to ${fqdn}"
    }

    @@kbp_ferm::rule { $real_name:
      prio       => $prio,
      interface  => $interface,
      outerface  => $outerface,
      saddr      => $saddr,
      daddr      => $daddr,
      proto      => $proto,
      icmptype   => $icmptype,
      sport      => $sport,
      dport      => $dport,
      jump       => $jump,
      action     => $action,
      table      => $table,
      chain      => $chain,
      ensure     => $ensure,
      exported   => false,
      fqdn       => $fqdn,
      ipaddress6 => $ipaddress6 ? {
        undef   => false,
        default => $ipaddress6,
      },
      tag        => $ferm_tag;
    }
  }
}
