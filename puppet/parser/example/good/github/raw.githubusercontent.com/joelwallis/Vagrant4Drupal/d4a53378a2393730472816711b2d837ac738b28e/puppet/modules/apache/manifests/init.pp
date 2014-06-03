class apache {
	package {
		'apache2':
			require => Exec['apt-get update'],
	}
	service {
		'apache2':
			ensure => running,
			enable => true,
			require => Package['apache2'],
	}
}
