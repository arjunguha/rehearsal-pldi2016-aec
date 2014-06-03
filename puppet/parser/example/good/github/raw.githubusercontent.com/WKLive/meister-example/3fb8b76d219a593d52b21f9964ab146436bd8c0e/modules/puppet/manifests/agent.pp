class puppet::agent ($server, $certname) {
  file { '/etc/puppet/puppet.conf':
    ensure => present,
    content => template("puppet/puppet-agent.conf.erb"),
    mode => '0444'
  }

  file { '/etc/default/puppet':
    ensure => present,
    source => 'puppet:///modules/puppet/default-puppet',
    mode => '0444'
  }

  service { "puppet":
    ensure =>  running,
    enable => true,
    require => [File['/etc/default/puppet'], File['/etc/puppet/puppet.conf']]
  }
}
