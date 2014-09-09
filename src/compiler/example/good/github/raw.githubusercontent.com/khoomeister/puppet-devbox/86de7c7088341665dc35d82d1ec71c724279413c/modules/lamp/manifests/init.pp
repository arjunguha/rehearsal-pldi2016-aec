class lamp ($rootPassword, $timezone, $user) {
	package { [
		'apache2',
		'libapache2-mod-proxy-html',
		'libapache2-mod-php5',
		'mysql-client',
		'mysql-server',
		'php-pear',
		'php5-cli',
		'php5-curl',
		'php5-gd',
		'php5-mcrypt',
		'php5-mysql'
	]:
		ensure => present,
	}

	exec { '/usr/sbin/a2enmod proxy':
		creates => '/etc/apache2/mods-enabled/proxy.load',
		user => root,

		require => Package['apache2'],
	}

	exec { '/usr/sbin/a2enmod proxy_http':
		creates => '/etc/apache2/mods-enabled/proxy_http.load',
		user => root,

		require => Package['apache2'],
	}

	exec { '/usr/sbin/a2enmod rewrite':
		creates => '/etc/apache2/mods-enabled/rewrite.load',
		user => root,

		require => Package['apache2'],
	}

	exec { '/usr/sbin/a2enmod vhost_alias':
		creates => '/etc/apache2/mods-enabled/vhost_alias.load',
		user => root,

		require => Package['apache2'],
	}

	file { '/www':
		ensure => link,
		target => '/var/www',

		require => Package['apache2'],
	}

	file { '/var/www':
		ensure => directory,
		group => 'www-data',
		mode => 2775,
		owner => $user,

		require => Package['apache2'],
	}

	file { '/var/www/localhost':
		ensure => directory,
		group => 'www-data',
		mode => 2775,
		owner => $user,

		require => File['/var/www'],
	}

	file { '/var/www/localhost/public':
		ensure => link,
		target => '/var/www',

		require => File['/var/www/localhost'],
	}

	file { '/etc/apache2/conf.d/charset':
		content => 'AddDefaultCharset UTF-8',
		group => root,
		mode => 644,
		owner => root,
		
		require => Package['apache2'],
	}

	file { '/etc/apache2/ports.conf':
		group => root,
		mode => 644,
		owner => root,
		source => 'puppet:///modules/lamp/ports.conf',

		require => Package['apache2'],
	}

	file { '/etc/apache2/sites-available/default':
		group => root,
		mode => 644,
		owner => root,
		source => 'puppet:///modules/lamp/default',

		require => Package['apache2'],
	}

	file { '/etc/php5/apache2/php.ini':
		content => template('lamp/php-apache2-ini.erb'),
		group => root,
		mode => 644,
		owner => root,

		require => Package['libapache2-mod-php5'],
	}

	exec { '/usr/bin/pear upgrade pear':
		require => Package['php-pear'],
		user => root,
	}

	exec { '/usr/bin/pecl install xdebug':
		unless => '/usr/bin/test -n "`find /usr/lib/php5/ -name xdebug.so`"',
		user => root,

		require => Exec['/usr/bin/pear upgrade pear'],
	}

	define discoverPearChannel {
		exec { "/usr/bin/pear channel-discover $name":
			onlyif => "/usr/bin/pear channel-info $name | grep \"Unknown channel\"",
			require => Exec['/usr/bin/pear upgrade pear'],
			user => root,
		}
	}
	discoverPearChannel { 'pear.phpunit.de': }
	discoverPearChannel { 'components.ez.no': }
	discoverPearChannel { 'pear.symfony-project.com': }

	exec { '/usr/bin/pear install pear.phpunit.de/PHPUnit':
		onlyif => "/usr/bin/pear info phpunit/PHPUnit | grep \"No information found\"",
		require => [
			Exec['/usr/bin/pear upgrade pear'],
			DiscoverPearChannel['pear.phpunit.de'],
			DiscoverPearChannel['components.ez.no'],
			DiscoverPearChannel['pear.symfony-project.com']
		],
		user => root,
	}

	file { '/var/www/myadmin.local':
		ensure => directory,
		group => 'www-data',
		owner => $user,
	}

	file { '/opt/packages/phpmyadmin-3.4.8.tar.gz':
		ensure => file,
		owner => root,
		group => root,
		source => 'puppet:///modules/lamp/phpmyadmin-3.4.8.tar.gz',
	}

	exec { 'untar phpmyadmin':
		command => '/bin/tar -xvzf /opt/packages/phpmyadmin-3.4.8.tar.gz',
		creates => '/var/www/myadmin.local/phpMyAdmin-3.4.8-all-languages',
		cwd => '/var/www/myadmin.local',
		group => root,
		user => root,

		require => File['/opt/packages/phpmyadmin-3.4.8.tar.gz'],
	}

	exec { '/bin/mv phpMyAdmin-3.4.8-all-languages public':
		cwd => '/var/www/myadmin.local',
		group => root,
		user => root,
		require => Exec['untar phpmyadmin'],
	}

	file { '/var/www/myadmin.local/public':
		ensure => directory,
		group => 'www-data',
		recurse => true,
		owner => $user,
		require => Exec['/bin/mv phpMyAdmin-3.4.8-all-languages public'],
	}

	appendLineToFile { 'Add myadmin.local to hosts':
		file => '/etc/hosts',
		line => '127.0.0.1 myadmin.local',
		user => root,

		require => File['/var/www/myadmin.local/public'],
	}

	exec { "/usr/bin/mysql -uroot -Dmysql -e \"UPDATE user SET Password=PASSWORD('$rootPassword') WHERE User='root'; FLUSH PRIVILEGES;\"":
		onlyif => '/usr/bin/mysql -uroot -e "SELECT TRUE"',
		require => Package['mysql-server'],
	}
}