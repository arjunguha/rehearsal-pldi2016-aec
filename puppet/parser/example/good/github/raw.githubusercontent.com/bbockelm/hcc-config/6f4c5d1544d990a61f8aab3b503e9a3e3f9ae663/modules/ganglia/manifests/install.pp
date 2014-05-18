class ganglia::install {

	package { $ganglia::params::ganglia_package_name:
		ensure => latest,
	}

	# we run gmond as a dedicated user
	group { "ganglia":
		name => "${ganglia::params::ganglia_group}",
		ensure => present,
		system => true,
	}

	user { "ganglia":
		name => "${ganglia::params::ganglia_user}",
		ensure => present,
		system => true,
		gid => "${ganglia::params::ganglia_group}",
		managehome => false,
		shell => '/sbin/nologin',
	}

}
