class ntp {

  package { 'ntp': ensure => installed }

  exec { 'ntp-update':
    command     => '/usr/sbin/ntpdate -u clock.isc.org',
    timeout     => 120,
    subscribe   => Package[ntp],
    refreshonly => true;
  }

  service { 'ntp':
    ensure     => running,
    enable     => true,
    hasstatus  => true,
    hasrestart => true,
    require    => Package[ntp];
  }

}
