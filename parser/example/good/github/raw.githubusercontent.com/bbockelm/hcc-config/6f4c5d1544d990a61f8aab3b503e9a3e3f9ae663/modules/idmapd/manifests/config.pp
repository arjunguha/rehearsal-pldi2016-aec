class idmapd::config {

	file { "idmapd.conf":
		path    => "${idmapd::params::idmapd_config_file}",
		mode    => "0644",
		owner   => "root",
		group   => "root",
		content => $lsbmajdistrelease ? {
			6 => template("idmapd/idmapd.conf-rhel6.erb"),
			default => template("idmapd/idmapd.conf-rhel5.erb"),
		},
		ensure  => present,
	}

}
