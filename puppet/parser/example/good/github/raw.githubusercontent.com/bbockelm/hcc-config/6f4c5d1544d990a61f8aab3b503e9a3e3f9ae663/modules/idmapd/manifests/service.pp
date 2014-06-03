class idmapd::service {

	service { "rpcidmapd":
		name       => "${idmapd::params::idmapd_service_name}",
		ensure     => running,
		enable     => true,
		hasrestart => true,
		hasstatus  => true,
		require    => Class["idmapd::config"],
		subscribe  => File["${idmapd::params::idmapd_config_file}"],
	}

}
