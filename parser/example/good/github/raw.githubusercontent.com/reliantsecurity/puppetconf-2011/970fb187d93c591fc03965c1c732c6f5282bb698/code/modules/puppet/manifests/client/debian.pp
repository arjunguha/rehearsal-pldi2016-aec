# = Class: puppet::client::debian
#
# == Description
#
# Overrides and debian-specfic resources 
#
# == Usage
# This class is meant to be included from the puppet::client class
class puppet::client::debian inherits puppet::client {

  include apt::sources

  package {
    facter:
      ensure => installed,
      require => Exec[apt-get_update];
    puppet: 
      ensure => $my_puppet_version,
      require => Package[puppet-common];
    puppet-common:
      ensure => $my_puppet_version,
      require => Exec[apt-get_update];
  }

	/* 
	This symlink provides a bridge between how puppet is packaged
	and what Debian expects. The puppet init script looks for 
	the PID file in /var/run/puppet.
	*/

	file { '/var/run/puppet': 
		ensure => '/var/puppet/run', 
		force => true,
	}

	Service[puppet] { hasstatus => true }

}
