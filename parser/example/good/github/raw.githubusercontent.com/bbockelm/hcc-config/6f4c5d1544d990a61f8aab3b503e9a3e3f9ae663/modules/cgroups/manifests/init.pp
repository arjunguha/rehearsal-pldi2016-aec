#
# Class: cgroups
#
# Manages cgroup configs
#

class cgroups {

	service { "cgconfig":
		name       => "cgconfig",
		ensure     => running,
		before     => Service["cgred"],
		enable     => true,
#		hasrestart => true,
		hasrestart => false,
		hasstatus  => true,
		require    => File["cgroup"],
	}

	service { "cgred":
		name       => "cgred",
		ensure     => running,
		enable     => true,
#		hasrestart => true,
		hasrestart => false,
		hasstatus  => true,
		require    => File["cgroup"],
	}


	# /cgroup stopped getting created automatically
	# somewhere between the R410 SL6 deploy and "now"
	# generate manually
	file { "cgroup":
		path    => "/cgroup",
		ensure  => directory,
	}

	# cgconfig won't start without correct attrs on /cgroup
	exec { "cgroup-selinux":
		command => "restorecon -R /cgroup",
		unless  => "ls -dZ /cgroup | grep cgroup_t",
	}


	file { "cgconfig.conf":
		path    => "/etc/cgconfig.conf",
		ensure  => present,
		owner   => "root", group => "root", mode => 644,
#		notify  => [ Service["cgconfig"], Service["cgred"] ],
		content => template("cgroups/cgconfig.conf.erb"),
	}

	file { "cgrules.conf":
		path    => "/etc/cgrules.conf",
		ensure  => present,
		owner   => "root", group => "root", mode => 644,
#		notify  => [ Service["cgconfig"], Service["cgred"] ],
		content => template("cgroups/cgrules.conf.erb"),
	}

}
