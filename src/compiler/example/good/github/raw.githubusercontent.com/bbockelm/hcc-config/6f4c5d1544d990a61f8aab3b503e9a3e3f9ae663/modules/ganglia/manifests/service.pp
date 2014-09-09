class ganglia::service {

	service { "gmond":
		name       => "${ganglia::params::ganglia_service_name}",
		ensure     => running,
		enable     => true,
		hasrestart => true,
		hasstatus  => true,
		require    => Class["ganglia::config"],
		subscribe  => File["${ganglia::params::ganglia_config_file}"],
	}

}
