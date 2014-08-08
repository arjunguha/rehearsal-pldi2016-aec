
class collectd::configure (
	$collectd_conf = $collectd::params::collectd_conf,
	$collection_conf = $collectd::params::collection_conf,
	$filters_conf = $collectd::params::filters_conf,
	$thresholds_conf = $collectd::params::thresholds_conf,
	$password_file = $collectd::params::password_file,
	$plugins = $collectd::params::plugins,
	$listen_address = "",
	$listen_port = "",
	$forward_address = "",
	$forward_port = "",
	$network_username = "",
	$network_password = "",
	$mysql_user = $collectd::params::mysql_user,
	$mysql_password = $collectd::params::mysql_password,
	$nginx_url = $collectd::params::nginx_url,
	$nginx_user = $collectd::params::nginx_user,
	$nginx_password = $collectd::params::nginx_password,
	$types_dbs = []
) inherits collectd::params {

	# Configuration derived from the parameters above
	$enable_network = ("$listen_address$forward_address" != "")
	$store_data = ("$forward_address" == "")

	file { $collectd_conf :
		ensure => file,
		content => template('collectd/collectd.conf.erb'),
	}

	file { $collection_conf :
		ensure => file,
		content => template('collectd/collection.conf.erb'),
	}

	file { $filters_conf :
		ensure => file,
		content => template('collectd/filters.conf.erb'),
	}

	file { $thresholds_conf :
		ensure => file,
		content => template('collectd/thresholds.conf.erb'),
	}

	if ($listen_address) {
		file { $password_file :
			ensure => file,
			content => "$network_username:$network_password\n",
		}
	}


	Class['collectd::install'] -> Class['collectd::configure']

}
