class system::hosts {
    file    {'/etc/hosts':
      ensure  => file,
      content => template('system/hosts.erb'),
      owner   => 'root',
      group   => 'root',
      mode    => '644',
    }
}