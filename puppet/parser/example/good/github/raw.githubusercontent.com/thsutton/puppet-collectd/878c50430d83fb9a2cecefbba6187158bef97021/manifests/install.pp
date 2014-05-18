class collectd::install (
	$packages = $collectd::params::packages
) inherits collectd::params {

	package { $packages :
		ensure => installed,
	}

}
