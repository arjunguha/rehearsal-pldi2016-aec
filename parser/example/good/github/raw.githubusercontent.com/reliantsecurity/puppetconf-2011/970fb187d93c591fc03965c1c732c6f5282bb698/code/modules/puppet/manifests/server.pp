# = Class: puppet::server
#
# == Description
#
# Puppet server component
#
# == Usage
#
# This class should not be used directly.
define puppet::server($owner = 'puppet', $group = 'root', $mode = 0750, $ensure = 'present', $rsync_minutes = [0, 30]) {

	include puppet::accounts

	# default file attributes
	File {
		owner => $owner,
		group => $group,
		mode => $mode,
    require => Class["puppet::accounts"],
	}

	tidy { "/var/puppet.${name}/log":
    recurse => true,
		age => '3d',
		size => '1g',
		type => 'ctime',
		matches => "*.log",
	}

	cron { 
    "rsync-slave-$name":
      ensure => absent,
      user => $owner,
      minute => $rsync_minutes,
      command => "/usr/local/sbin/rsync-puppet-slave.sh $name";
    "puppet-slave-rsync-$name":
      ensure => $ensure,
      user => $owner,
      minute => $rsync_minutes,
      command => "/usr/local/sbin/puppet_slave_rsync.sh $name";
	}

	file { 
		"/var/puppet.$name":
			ensure => $ensure ? {
        present => directory,
        default => absent,
      },
			owner => 'root', 
			group => 'root',
			mode => 0755;
		[ 
		"/var/puppet.${name}/server_data",
		"/var/puppet.${name}/bucket",
		"/var/puppet.${name}/facts",
		"/var/puppet.${name}/lib",
		"/var/puppet.${name}/reports",
		"/var/puppet.${name}/log",
		"/var/puppet.${name}/rrd",
		"/var/puppet.${name}/yaml"
		]: 
			ensure => $ensure ? {
        present => directory,
        default => absent,
      },
			owner => 'puppet', 
			group => 'puppet'; 
		"/var/puppet.${name}/yaml/node":
			ensure => $ensure ? {
        present => directory,
        default => absent,
      },
			owner => 'puppet', 
			group => 'root', 
			mode => 0755;
		"/var/puppet.${name}/yaml/facts":
			ensure => $ensure ? {
        present => directory,
        default => absent,
      },
			owner => 'puppet', 
			group => 'root', 
			mode => 0755;
		"/var/puppet.${name}/run":
			ensure => $ensure ? {
        present => directory,
        default => absent,
      },
			owner => 'puppet', 
			group => 'root', 
			mode => 1777;
		"/var/puppet.${name}/state":
			ensure => $ensure ? {
        present => directory,
        default => absent,
      },
			owner => 'puppet', 
			group => 'root', 
			mode => 1755;
		"/etc/puppet.$name":
			ensure => $ensure ? {
        present => directory,
        default => absent,
      },
			mode => 0644,
			recurse => true;
		"/etc/puppet.$name/puppet.conf":
			ensure => absent;
	}

}
