package { 'collectd':
  ensure  => latest,
  require => Package['epel-release'],
}

package { 'collectd-rrdtool':
  ensure  => latest,
  require => Package['collectd'],
}

file { 'collectd_swap':
  ensure  => file,
  path    => '/etc/collectd.d/swap.conf',
  require => Package['collectd'],
}

package { 'epel-release':
  ensure   => present,
  before => File["collectd_swap"]
}

