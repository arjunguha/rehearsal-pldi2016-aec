#
# Class: autofs
#
# manages autofs (master and maps)
#
class autofs {

	package { autofs: name => "autofs", ensure => present }

	$auto_master = '/etc/auto.master'

	service { "autofs":
		name       => "autofs",
		ensure     => running,
		enable     => true,
		hasrestart => true,
		hasstatus  => true,
		require    => Package["autofs"],
		subscribe  => File[$auto_master],
	}

	concat { $auto_master:
		owner   => 'root',
		group   => 'root',
		mode    => '0644',
   }

	concat::fragment { 'auto_master_base':
		target  => $auto_master,
		content => inline_template(file("/etc/puppet/modules/autofs/templates/auto.master-$hostname.erb", "/etc/puppet/modules/autofs/templates/auto.master.erb")),
		order   => 01
	}
		
	file { "autofs.red":
		path    => "/etc/auto.red",
		mode    => 644,
		owner   => "root",
		group   => "root",
		content => inline_template(file("/etc/puppet/modules/autofs/templates/auto.red-$hostname.erb", "/etc/puppet/modules/autofs/templates/auto.red.erb")),
		require => Package[autofs],
		notify  => Service[autofs],
		ensure  => present,
	}

	file { "/etc/sysconfig/autofs":
		mode    => 644,
		owner   => "root",
		group   => "root",
	   source => "puppet:///modules/autofs/autofs.verbose",	
		require => Package[autofs],
		notify  => Service[autofs],
		ensure  => present,
	}
}

# used by other modules to append lines to /etc/auto.master
define autofs::add_map($map, $mountpoint, $options='') {

	concat::fragment { "autofs::mount :${mountpoint}:${map}":
		target  => '/etc/auto.master',
		content => "$mountpoint $map $options\n",
		order   => 10,
   }

}
