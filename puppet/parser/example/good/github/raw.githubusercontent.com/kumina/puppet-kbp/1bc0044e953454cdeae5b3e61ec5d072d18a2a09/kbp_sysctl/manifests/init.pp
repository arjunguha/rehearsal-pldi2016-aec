# Author: Kumina bv <support@kumina.nl>

# Class: kbp_sysctl
#
# Actions:
#  Undocumented
#
# Depends:
#  sysctl
#  gen_puppet
#
class kbp_sysctl {
  include sysctl

  sysctl::setting {
    'kernel.panic':
      value => 30;
    'kernel.panic_on_oops':
      value => 1;
    # Disable all IPv6 autoconfiguration
    ['net.ipv6.conf.default.autoconf', 'net.ipv6.conf.default.accept_ra', 'net.ipv6.conf.default.accept_ra_defrtr',
     'net.ipv6.conf.default.accept_ra_rtr_pref', 'net.ipv6.conf.default.accept_ra_pinfo', 'net.ipv6.conf.default.accept_source_route',
     'net.ipv6.conf.default.accept_redirects', 'net.ipv6.conf.all.autoconf', 'net.ipv6.conf.all.accept_ra',
     'net.ipv6.conf.all.accept_ra_defrtr', 'net.ipv6.conf.all.accept_ra_rtr_pref', 'net.ipv6.conf.all.accept_ra_pinfo',
     'net.ipv6.conf.all.accept_source_route', 'net.ipv6.conf.all.accept_redirects']:
      value => '0';
    # Always allow memory allocation, since that's more deterministic.
    'vm.overcommit_memory':
      value => '1';
    # Keep swapping to a minimum, since it's generally unnecessary.
    'vm.swappiness':
      value => '10';
  }
}
