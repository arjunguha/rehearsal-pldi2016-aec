# Class: collectd::service
#
# Manages the collectd service.
#
class collectd::service inherits collectd::params {

	service { 'collectd' :
		enable => true,
		ensure => running,
		hasstatus => true,
		hasrestart => true,
	}

	Class['collectd::configure'] ~> Class['collectd::service']
	Class['collectd::configure'] -> Class['collectd::service']

}
