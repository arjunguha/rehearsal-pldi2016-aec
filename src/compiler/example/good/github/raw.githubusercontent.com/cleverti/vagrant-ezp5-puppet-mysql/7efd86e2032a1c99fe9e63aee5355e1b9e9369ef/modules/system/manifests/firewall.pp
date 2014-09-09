class system::firewall {
    file    {'/etc/sysconfig/iptables':
      ensure  => file,
      content => template('system/iptables.erb'),
      owner   => 'root',
      group   => 'root',
      mode    => '600',
    }
    service { iptables:
      ensure => running,
      subscribe => File["/etc/sysconfig/iptables"],
    }
}