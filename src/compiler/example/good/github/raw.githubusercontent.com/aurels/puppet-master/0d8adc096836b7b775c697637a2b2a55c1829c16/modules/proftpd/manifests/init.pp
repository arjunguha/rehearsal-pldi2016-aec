class proftpd {
  package { 'proftpd':
    ensure => present,
    before => File['/etc/proftpd/proftpd.conf'],
  }

  file { '/etc/proftpd/proftpd.conf':
    ensure  => file,
    mode    => 622,
    content => template('proftpd/proftpd.conf.erb'),
  }

  service { 'proftpd':
    ensure     => running,
    enable     => true,
    hasrestart => true,
    hasstatus  => true,
    subscribe  => File['/etc/proftpd/proftpd.conf'],
  }
}
