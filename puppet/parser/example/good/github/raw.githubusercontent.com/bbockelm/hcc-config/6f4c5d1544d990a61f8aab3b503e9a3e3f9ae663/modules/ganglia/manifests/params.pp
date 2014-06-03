class ganglia::params {

	$ganglia_package_name = [ 'ganglia-gmond', 'ganglia-gmond-modules-python', 'libganglia' ]
	$ganglia_service_name = "gmond"
	$ganglia_process_name = "gmond"
	$ganglia_config_file = "/etc/ganglia/gmond.conf"

	$ganglia_user = "ganglia"
	$ganglia_group = "ganglia"

}
