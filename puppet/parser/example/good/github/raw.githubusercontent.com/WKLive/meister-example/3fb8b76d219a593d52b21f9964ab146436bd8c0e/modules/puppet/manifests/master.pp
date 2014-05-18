class puppet::master ($server, $certname) {
  file { '/etc/puppet/puppet.conf':
    ensure => present,
    content => template("puppet/puppet-master.conf.erb"),
    mode => '0444'
  }

  file { '/etc/default/puppet':
    ensure => present,
    source => 'puppet:///modules/puppet/default-puppet',
      mode => '0444'
  }
}
