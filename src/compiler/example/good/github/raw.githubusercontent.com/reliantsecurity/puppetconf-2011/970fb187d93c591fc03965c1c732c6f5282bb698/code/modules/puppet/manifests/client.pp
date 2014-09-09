# = Class: puppet::client
#
# == Description
#
# Manage all aspects of the Puppet client 
# - software package(s)
# - client daemon
# - puppet.conf
class puppet::client {

	$cron_puppet_client_minutes = [ 3, 8, 13, 18, 23, 28, 33, 38, 43, 48, 53, 58 ]
	$cron_puppet_client_lock_cleanup_minutes = [ 10, 30, 50 ]

	include ruby

	# Each supported client OS goes here
	case $operatingsystem {
		solaris: { include puppet::client::solaris }
		debian: { include puppet::client::debian }
	}

	service { puppet:
    enable => running,
    ensure => stopped,
    subscribe => [ Package[puppet], File[puppet-conf] ],
	}

	file { puppet-conf:
    path => '/etc/puppet/puppet.conf',
    ensure => present,
    owner => 'root', 
    group => 'root', 
    mode => 0644,
    require => Package[puppet],
    content => template("puppet/client/global/puppet.conf.erb");
	}

}
