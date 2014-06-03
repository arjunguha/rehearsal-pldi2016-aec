class mysql {
	$mysql_password = 'vagrant4drupal'

	package {
		'mysql-server':
			require => Exec['apt-get update'],
	}

	service {
		'mysql':
			enable => true,
			ensure => running,
			require => Package['mysql-server'],
	}
}
