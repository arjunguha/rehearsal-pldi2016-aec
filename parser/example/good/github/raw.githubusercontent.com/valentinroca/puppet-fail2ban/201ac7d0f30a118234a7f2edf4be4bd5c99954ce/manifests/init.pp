# Class: fail2ban
#
# This module manages fail2ban service and its main configuration files.
#
# Sample Usage: include fail2ban
#
class fail2ban {

  package { 'fail2ban': ensure => installed }

  service { 'fail2ban': 
    ensure  => running,
    require => Package['fail2ban'],
  }

  file { '/etc/fail2ban/fail2ban.conf':
    owner   => 'root',
    group   => 'root',
    mode    => '0644',
    source  => 'puppet:///modules/fail2ban/fail2ban.conf',
    require => Package['fail2ban'],
  }

  file { '/etc/fail2ban/jail.conf':
    owner   => 'root',
    group   => 'root',
    mode    => '0644',
    source  => "puppet:///modules/fail2ban/jail-$operatingsystem.conf",
    require => Package['fail2ban'],
  }

  exec { '/etc/init.d/fail2ban restart':
    subscribe   => [ File['/etc/fail2ban/fail2ban.conf'], File['/etc/fail2ban/jail.conf'] ],
    refreshonly => true,
  }

}
