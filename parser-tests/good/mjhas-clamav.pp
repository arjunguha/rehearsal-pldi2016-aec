# From https://github.com/mjhas/clamav
# Replaced Package[x, y] syntax with [Package[x], Package[y]]
# Modified user resource slightly.

include clamav
package { 'amavisd-new':
  ensure => latest
}

## init.pp

class clamav(
  $milter=false,
  $amavis=true,
) {
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
  if $amavis {
    user {'clamav':
      ensure  => present,
      # gid     => 'clamav',
      groups  => 'amavis',
      require => [Package['clamav-daemon'], Package['amavisd-new']],
      notify  => Service['clamav-daemon'],
    }
  }
  service {'clamav-freshclam':
    ensure  => running,
    require => Package['clamav-freshclam']
  }
  if $milter {
    package {'clamav-milter':
      ensure  => latest,
      require => Package['clamav-daemon'],
    }
    service {'clamav-milter':
      ensure  => running,
      require => Package['clamav-milter']
    }
  }
}
