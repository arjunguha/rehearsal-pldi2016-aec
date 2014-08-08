# vim: ts=2: sw=2
Exec { 
	path => $operatingsystem ? {
		solaris => "/opt/csw/bin:/opt/csw/sbin:/usr/bin:/usr/sbin:/bin:/sbin:/usr/gnu/bin", 
		default => "/usr/local/bin:/usr/local/sbin:/usr/bin:/usr/sbin:/bin:/sbin", 
	}
}

# If solaris, always use the blastwave provider
# see package_managers::pkg-get for dependencies
Package {
	provider => $operatingsystem ? {
		solaris => blastwave,
		debian => apt,
	},
	adminfile => $operatingsystem ? {
		solaris => "/var/pkg-get/admin",
		default => undef,
	},
}

# Load all styles and roles for the site
import "nodes/*/*.pp"
