# == Class: freebsd::src
#
# This code is meant to configure a *physical* interface on a FreeBSD system.
# You should be able to set the v4 and v6 addresses, as well as set the MTU
# for a given interface.
#
# You may also wish to only set the MTU and bring up the interface, which can
# be useful when you want ot assign a given interface to a lagg, but also
# want a custom MTU.
#
# An option is provided here for $alias.  This is used to add virtual
# addresses to a physicial interface.
#
# == Paramaters
#
# [*address*]
#   The IPv4 address to assign to the interface (CIDR notation).
#   Can also set to 'DHCP' for a dhcp interface
# [*v6address*]
#   The IPv6 address to assign to the interface (Prefix Notation).
# [*mtu*]
#   Set the MTU of the physical interface.
# [*is_alias*]
#   Aliases are addresses in addition to the primary (bool)
# [*description*]
#   An interface label
#
# == Examples
#
#  class { "freebsd::interface":
#    address   => '10.127.0.1/30',
#    v6address => '2001:dead:beef:1::/64',
#    mtu       => '9000',
#  }
#
# == Authors
#
# Zach Leslie <xaque208@gmail.com>
#
# == Copyright
#
# Copyright 2013 Puppet Labs
#
define freebsd::network::interface (
  $address     = '',
  $v6address   = '',
  $mtu         = '',
  $is_alias    = false,
  $description = undef,
) {

  # We will only be working with rc.conf here
  Shell_config { file => '/etc/rc.conf' }

  # Set the mtu string to be used in rc.conf if we've set it
  if ( $mtu != '' ) {
    $mtu_string = " mtu ${mtu}"
  }

  if $description {
    $description_string += " description \'${description}\'"
  }

  # When the addresses being assigned are aliases, they should not have the
  # address family in the ifconfig line.  Here, we set the address family
  # string only if we are not building an alias.
  unless ( $is_alias ) {
    $inet_string  = "inet "
    $inet6_string = "inet6 "
  }

  # We should only be setting the addresses if we have specified either a v4 or
  # v6 address.
  if ($address != '') or ($v6address != '') {

    # Configure the v4 address in rc.conf if we have set one.
    if $address != '' {
      shell_config { "ifconfig ${name}":
        key   => "ifconfig_${name}",
        value => "${inet_string}${address}${mtu_string}${description_string}",
      }
    }

    # Configure DHCP on v4
    if $address == 'DHCP' {
      shell_config { "ifconfig ${name}":
        key   => "ifconfig_${name}",
        value => "DHCP",
      }
    }

    # Configure the v6 address in rc.conf if we have set one.
    if $v6address != '' {
      shell_config { "v6ifconfig ${name}":
        key   => "ifconfig_${name}_ipv6",
        value => "${inet6_string}${v6address}${mtu_string}${description_string}",
      }
    }

  } else {

    # We arrive here only when we care only to set the mtu, but not the
    # addresses.  This is usefil for LAGG interfaces.
    if $mtu != '' {
      shell_config { "ifconfig mtu ${name}":
        key   => "ifconfig_${name}",
        value => "${mtu_string} up",
      }
    }

  }
}
