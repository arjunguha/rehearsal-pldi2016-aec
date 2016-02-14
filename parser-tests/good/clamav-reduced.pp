package { 'amavisd-new':
  ensure => latest
}

package {'clamav-daemon':
  ensure  => latest
}
package {'clamav-freshclam':
  ensure  => latest,
  require => Package['clamav-daemon'],
}

service {'clamav-daemon':
  ensure  => running,
  require => Package['clamav-daemon']
}


service {'clamav-freshclam':
  ensure  => running,
  require => Package['clamav-freshclam']
}

user {'clamav':
  ensure  => present,
  groups  => 'amavis',
  require => [Package['clamav-daemon'], Package['amavisd-new']],
  notify  => Service['clamav-daemon'],
}
