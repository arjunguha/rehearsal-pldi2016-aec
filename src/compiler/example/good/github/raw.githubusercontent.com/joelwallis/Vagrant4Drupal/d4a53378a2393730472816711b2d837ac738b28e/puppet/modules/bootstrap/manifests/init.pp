class bootstrap {

	# Development tools
	$dev_packages = ['git', 'puppet-common']
	package {
		$dev_packages:
			require => Exec['apt-get update'],
	}

	# Useful tools
	$useful_packages = ['htop']
	package {
		$useful_packages:
			require => Exec['apt-get update'],
	}
}
