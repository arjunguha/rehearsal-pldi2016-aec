class php {
	$php_packages = ['php5', 'php5-cli', 'php5-curl', 'php5-gd', 'php5-mcrypt', 'php5-mysql', 'php5-sqlite', 'php-pear']
	package {
		$php_packages:
			require => Exec['apt-get update'],
	}

	$apache_bridge_packages = ['libapache2-mod-php5']
	package { $apache_bridge_packages:
		require => Package['php5'],
	}
}
