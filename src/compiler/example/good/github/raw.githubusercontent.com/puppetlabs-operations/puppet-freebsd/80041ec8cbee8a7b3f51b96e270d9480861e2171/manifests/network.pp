# == Class: freebsd::network
#
# Configures various network paramaters on a FreeBSD system.
#
# == Paramaters
#
# [*gateway_enable*]
#   Route IPv4 traffic between interfaces?
# [*ipv6*]
#   Enable IPv6?
# [*ipv6_gateway_enable*]
#   Route IPv6 traffic between interfaces?
# [*defaultrouter*]
#   Sets the default IPv4 router for this machine.
# [*ipv6_defaultrouter*]
#   Sets the default IPv6 router for this machine.
#
# == Examples
#
#  class { "freebsd::network": }
#
# == Authors
#
# Zach Leslie <xaque208@gmail.com>
#
# == Copyright
#
# Copyright 2013 Puppet Labs
#
class freebsd::network (
  $gateway_enable      = false,
  $ipv6                = true,
  $ipv6_gateway_enable = false,
  $defaultrouter       = '',
  $ipv6_defaultrouter  = ''
){

  Shell_config { file => '/etc/rc.conf' }

  if $gateway_enable {
    shell_config { "gateway_enable":
      key   => 'gateway_enable',
      value => "YES",
    }
  } else {
    shell_config { "gateway_enable":
      ensure => absent,
      key    => 'gateway_enable',
      value  => "YES",
    }
  }

  if $ipv6_enable {
    shell_config { "ipv6_enable":
      key   => 'ipv6_enable',
      value => "YES",
    }
  } else {
    shell_config { "ipv6_enable":
      ensure => absent,
      key    => 'ipv6_enable',
      value  => "YES",
    }
  }

  if $ipv6_gateway_enable {
    shell_config { "ipv6_gateway_enable":
      key   => 'ipv6_gateway_enable',
      value => "YES",
    }
  } else {
    shell_config { "ipv6_gateway_enable":
      ensure => absent,
      key    => 'ipv6_gateway_enable',
      value  => "YES",
    }
  }

  if $defaultrouter != '' {
    shell_config { "defaultrouter":
      key   => 'defaultrouter',
      value => "${defaultrouter}",
    }
  } else {
    shell_config { "defaultrouter":
      ensure => absent,
      key    => 'defaultrouter',
      value  => "${defaultrouter}",
    }
  }

  if $ipv6_defaultrouter {
    shell_config { "ipv6_defaultrouter":
      key   => 'ipv6_defaultrouter',
      value => "${ipv6_defaultrouter}",
    }
  } else {
    shell_config { "ipv6_defaultrouter":
      ensure => absent,
      key    => 'ipv6_defaultrouter',
      value  => "${ipv6_defaultrouter}",
    }
  }
}
