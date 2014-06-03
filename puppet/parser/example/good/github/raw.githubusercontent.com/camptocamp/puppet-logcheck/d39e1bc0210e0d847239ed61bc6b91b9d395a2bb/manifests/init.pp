class logcheck {
  # install package
  package {'logcheck':
    ensure => present,
  }

  # config
  file {'/etc/logcheck/logcheck.conf':
    ensure  => present,
    content => template('logcheck/logcheck.conf.erb'),
    require => Package['logcheck'],
    owner   => root,
    group   => logcheck,
  }

  concat {[
      '/etc/logcheck/logcheck.logfiles',
      '/etc/logcheck/cracking.ignore.d/auto-puppet',
      '/etc/logcheck/ignore.d.paranoid/auto-puppet',
      '/etc/logcheck/ignore.d.server/auto-puppet',
      '/etc/logcheck/ignore.d.workstation/auto-puppet',
      '/etc/logcheck/violations.ignore.d/auto-puppet'
    ]:
    owner   => root,
    group   => logcheck,
    mode    => '0644',
    force   => true,
    require => Package['logcheck'],
  }

  file {'/etc/logcheck/logcheck.logfiles':
    owner   => root,
    group   => logcheck,
    mode    => '0640',
  }
}
