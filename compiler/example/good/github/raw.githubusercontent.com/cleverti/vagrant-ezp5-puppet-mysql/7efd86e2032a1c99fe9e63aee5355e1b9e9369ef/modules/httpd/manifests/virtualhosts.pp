class httpd::virtualhosts {
    file    {'/etc/httpd/conf.d/02.namevirtualhost.conf':
      ensure  => file,
      content => template('httpd/02.namevirtualhost.conf.erb'),
      owner   => 'root',
      group   => 'root',
      mode    => '644',
      require => Package["httpd"],
    }
    file    {'/etc/httpd/conf.d/ezp5.conf':
      ensure  => file,
      content => template('httpd/ezp5.conf.erb'),
      owner   => 'root',
      group   => 'root',
      mode    => '644',
      require => Package["httpd"],
    }
}