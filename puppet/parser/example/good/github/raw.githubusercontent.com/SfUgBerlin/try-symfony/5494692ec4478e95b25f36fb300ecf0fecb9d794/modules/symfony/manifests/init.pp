class symfony {
	
	include symfony::params
	
	# yes, we need git
	package { "git-core": }
	
	# remove symfony dir
	file { "${symfony::params::root_dir}":
		ensure  => absent,
	}

	# download symfony standard
  	exec { "download":
		command => "git clone ${symfony::params::download_url} ${symfony::params::root_dir}",
		require => Package["git-core", "apache"],
		creates => "${symfony::params::root_dir}",
	}

	# remove .git file
	file { "${symfony::params::root_dir}/.git":
		ensure => absent,
    	force  => true,
	}	
}


	