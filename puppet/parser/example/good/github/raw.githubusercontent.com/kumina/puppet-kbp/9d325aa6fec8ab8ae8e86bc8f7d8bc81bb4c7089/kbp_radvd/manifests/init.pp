#
# Class: kbp_radvd
#
# Actions:
#  Install radvd and set some sysctl stuff to allow IPv6 forwarding.
#  This class is called from kbp_radvd::prefix and doesn't need to be included directly.
#
# Depends:
#  sysctl
#
class kbp_radvd {
  include sysctl
  sysctl::setting {
    ['net.ipv6.conf.default.forwarding', 'net.ipv6.conf.all.forwarding']:
      value => '1';
  }

  kbp_ferm::rule { 'Respond to router solicitations_v6':
    proto    => 'icmpv6',
    icmptype => 'router-solicitation',
    action   => 'ACCEPT';
  }
}

#
# Define: kbp_radvd::prefix
#
# Actions:
#  Setup a Router Advertisment for a prefix on an interface.
#
# Parameters:
#  interface:
#   The interface the advertisment should be sent out on.
#  prefix:
#   The IPv6 prefix (in the form of 1:2:2:3::/64) to be announced on this interface
#  rdnss:
#   An (optional) array of recursive DNS servers that should be announced
#  dnssl:
#   An (optional) array of DNS search domains that should be announced
#
# Depends:
#  kbp_radvd
#
define kbp_radvd::prefix ($interface, $prefix, $rdnss=false, $dnssl=false) {
  include kbp_radvd
  gen_radvd::prefix { $name:
    interface => $interface,
    prefix    => $prefix,
    rdnss     => $rdnss,
    dnssl     => $dnssl;
  }
}
