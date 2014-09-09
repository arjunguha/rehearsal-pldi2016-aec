class ganglia::config {

	file { "gmond.conf":
		path    => "${ganglia::params::ganglia_config_file}",
		mode    => "0644",
		owner   => "root",
		group   => "root",
		content => template("ganglia/gmond.conf.erb"),
		require => Class["ganglia::install"],
		ensure  => present,
	}

}
