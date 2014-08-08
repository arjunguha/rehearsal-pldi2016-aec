define udev::ifcfg ($originaldevice) {

  if ! defined(File["/etc/sysconfig/network-scripts/ifcfg-${name}"]) { 
    file { "/etc/sysconfig/network-scripts/ifcfg-${name}":
      ensure  => present,
      content => template('udev/ifcfg-eth.erb'),
      owner   => 'root',
      group   => 'root',
      mode    => '0644',
    }
  } else {
    File["/etc/sysconfig/network-scripts/ifcfg-${name}"] {
      ensure  => present,
      content => template('udev/ifcfg-eth.erb'),
      owner   => 'root',
      group   => 'root',
      mode    => '0644',
    }
  }
  if ! defined(File["/etc/sysconfig/network-scripts/ifcfg-${originaldevice}"]) {
    file { "/etc/sysconfig/network-scripts/ifcfg-${originaldevice}":
      ensure => absent, 
    } 
  } else {
    File ["/etc/sysconfig/network-scripts/ifcfg-${originaldevice}"] {
        ensure => absent,
    }
  }
}
