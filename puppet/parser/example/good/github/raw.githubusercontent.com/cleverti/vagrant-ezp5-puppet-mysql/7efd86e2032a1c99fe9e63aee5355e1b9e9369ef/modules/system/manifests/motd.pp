class system::motd {
    file    {'/etc/motd':
      ensure  => file,
      content => template('system/motd.erb'),
      owner   => 'root',
      group   => 'root',
      mode    => '644',
    }
}