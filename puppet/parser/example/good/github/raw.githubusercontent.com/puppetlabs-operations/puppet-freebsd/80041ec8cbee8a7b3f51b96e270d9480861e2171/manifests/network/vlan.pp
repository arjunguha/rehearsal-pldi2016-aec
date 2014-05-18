define freebsd::network::vlan (
  $ensure    = 'present',
  $address   = '',  # CIDR Notation
  $v6address = '',  # Address only
  $prefixlen = '',  # Prefix length for v6 address
  $vlan,
  $dev,
){

  # Manage the configuration of a FreeBSD vLAN interface.

  # Set the interface name to be used in rc.conf
  $ifname = "vlan${vlan}"

  # We should take the correct action
  if ($ensure == 'present') {

    # Add the v4 ifconfig line to rc.conf if we've set an address.
    if $address != '' {
      $vlan_string = " vlan ${vlan} vlandev ${dev}"
      shell_config { "subnet_vlan_${name}_${ifname}":
        file  => '/etc/rc.conf',
        key   => "ifconfig_${ifname}",
        value => "inet ${address}${vlan_string}",
      }
    }

    # Add the v6 ifconfig line to rc.conf if we've set an address.
    if $v6address != '' {
      # If we have not set a v4 address, then we need to configure the vlan on
      # the v6 address.  This is because the vlan information can only be set
      # once, either on the v4 or the v6 address, but not both.
      if $address == '' {
        $v6_vlan_string = " vlan ${vlan} vlandev ${dev}"
      } else {
        $v6_vlan_string = ""
      }
      # Add the v6 ifconfig line to rc.conf.
      shell_config { "subnet_vlan_${name}_${ifname}_ipv6":
        file  => '/etc/rc.conf',
        key   => "ifconfig_${ifname}_ipv6",
        value => "inet6 ${v6address}${v6_vlan_string}",
        }
    }

    # Create the vlan interface.  This is needed because the interface is
    # virtual, and creation of virtual interfaces is only done on boot trough
    # the rc variable 'cloned_interfaces'.  As such, if we wish to use it now,
    # we must create it so that we may do address assignment.
    exec { "create_interface_${name}_${ifname}":
      unless  => "/sbin/ifconfig ${ifname}",
      command => "/sbin/ifconfig ${ifname} create",
      notify  => Exec["start_vlan_${name}_${ifname}"],
      require => Shell_config["subnet_vlan_${name}_${ifname}"],
    }

    # Start the vlan interface.  This does the actuall address assignment.
    # Running netif start on an interface reads the configuration from rc.conf
    # and proceed accordingly.
    exec { "start_vlan_${name}_${ifname}":
      refreshonly => true,
      command     => "/usr/sbin/service netif start ${ifname}",
      require     => Exec["create_interface_${name}_${ifname}"],
    }

  } elsif ($ensure == 'absent'){
  }
}
