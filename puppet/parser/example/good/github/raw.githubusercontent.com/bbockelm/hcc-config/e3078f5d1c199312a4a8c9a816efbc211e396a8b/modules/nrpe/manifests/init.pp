#
# Class: nrpe
#

class nrpe {

	package { "nrpe": ensure => present, }
	package { "nagios-plugins-all": ensure => present, }
	package { "megaraid-cli": ensure => present, }

	service { "nrpe":
		ensure => running,
		enable => true,
		hasrestart => true,
		hasstatus => true,
		require => [ Package["nrpe"], File["sudo-nrpe"], ],
		subscribe => File["nrpe.cfg"],
	}

	file { "nrpe.cfg":
		path => "/etc/nagios/nrpe.cfg",
		owner => "root", group => "root", mode => 644,
		content => template("nrpe/nrpe.cfg.erb"),
		require => Package["nrpe"],
		notify => Service["nrpe"],
	}

	file { "sudo-nrpe":
		path => "/etc/sudoers.d/sudo-nrpe",
		owner => "root", group => "root", mode => 0440,
		require => Class["sudo"],
		source => "puppet:///modules/nrpe/sudo-nrpe",
	}

	file { "check_host_cert":
		path => "/usr/lib64/nagios/plugins/check_host_cert",
		owner => "root", group => "root", mode => 755,
		source => $lsbmajdistrelease ? {
			5       => "puppet:///modules/nrpe/check_host_cert.el5",
			default => "puppet:///modules/nrpe/check_host_cert",
		},
		require => Package["nagios-plugins-all"],
	}

	file { "check_megaraid_sas":
		path => "/usr/lib64/nagios/plugins/check_megaraid_sas",
		owner => "root", group => "root", mode => 755,
		source => "puppet:///modules/nrpe/check_megaraid_sas",
		require => Package["nagios-plugins-all"],
	}

	file { "check_mountpoints":
		path => "/usr/lib64/nagios/plugins/check_mountpoints",
		owner => "root", group => "root", mode => 755,
		seltype => "nagios_checkdisk_plugin_exec_t",
		source => "puppet:///modules/nrpe/check_mountpoints",
		require => Package["nagios-plugins-all"],
	}
	file { "check_sssd":
		path => "/usr/lib64/nagios/plugins/check_sssd",
		owner => "root", group => "root", mode => 755,
		source => "puppet:///modules/nrpe/check_sssd",
		require => Package["nagios-plugins-all"],
      seltype => 'nagios_unconfined_plugin_exec_t',
	}
	file { "check_node_health":
		path => "/usr/lib64/nagios/plugins/check_node_health",
		owner => "root", group => "root", mode => 755,
		source => "puppet:///modules/nrpe/check_node_health",
		require => Package["nagios-plugins-all"],
	}

	file { "check_puppet":
		path => "/usr/lib64/nagios/plugins/check_puppet",
		owner => "root", group => "root", mode => 755,
		# Cannot read puppet files otherwise
		seltype => "nagios_unconfined_plugin_exec_t",
		source => "puppet:///modules/nrpe/check_puppet",
		require => Package["nagios-plugins-all"],
	}

# breaks non-worker things, really gotta unravel all this at some point
# no idea why, nor time to look today \o/     - garhan
#
# It's b/c that context doesn't exist on RHEL5.  What to do...what to do....

#	class { "selinuxmodules::fcontext":
#				context => "nagios_exec_t",
#				pathname => "/usr/lib64/nagios/plugins/check_sssd",
#			}
	
#	class { "selinuxmodules::fcontext":
#				context => "nagios_unconfined_plugin_exec_t",
#				pathname => "/usr/lib64/nagios/plugins/check_sssd",
#			}
	
}
