# https://github.com/duritong/puppet-shorewall/blob/07c863098f453d3ce67d64c2ac5c67d8cf4c6a25/manifests/init.pp#L5
# Stolen from the init.pp
$shorewall::ensure_version = 'present'
$shorewall::conf_source = false

package { 'shorewall':
  ensure => $shorewall::ensure_version,
}

file {
  '/etc/shorewall/shorewall.conf':
    require => Package["shorewall"],
    notify  => Service["shorewall"],
    owner   => 'root',
    group   => 'root',
    mode    => '0644'
}

file {
  '/etc/shorewall/puppet':
    ensure  => directory,
    require => Package["shorewall"],
    owner   => 'root',
    group   => 'root',
    mode    => '0644'
}

if $shorewall::conf_source {
  File['/etc/shorewall/shorewall.conf']
} else {

  augeas { 'shorewall_module_config_path':
    changes => 'set /files/etc/shorewall/shorewall.conf/CONFIG_PATH /etc/shorewall/puppet:/etc/shorewall:/usr/share/shorewall',
    lens    => 'Shellvars.lns',
    incl    => '/etc/shorewall/shorewall.conf',
    notify  => Service['shorewall'],
    require => Package['shorewall']
  }
}

service{'shorewall':
  ensure      => running,
  enable      => true,
  hasstatus   => true,
  hasrestart  => true,
  require     => Package['shorewall'],
}
