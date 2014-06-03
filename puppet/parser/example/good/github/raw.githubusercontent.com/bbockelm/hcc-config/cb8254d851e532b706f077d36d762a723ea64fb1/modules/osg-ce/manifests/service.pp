class osg-ce::service {

	$require = Class["osg-ce::config"]

	$ce_service_name = [ 'globus-gatekeeper', 'osg-info-services', 'globus-gridftp-server', 'gratia-probes-cron', 'osg-cleanup-cron' ]
	service { $ce_service_name:
		ensure => running,
		hasstatus => true,
		hasrestart => true,
		enable => true,
		require => Class["osg-ce::config"],
	}

}
