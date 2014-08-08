class ruby {
	package { [
		'ruby',
		'ruby1.9.1',
		'rubygems',
	]:
		ensure => present,
	}

	exec { '/usr/bin/update-alternatives --set ruby /usr/bin/ruby1.9.1':
		unless => '/usr/bin/test "`/bin/readlink /etc/alternatives/ruby`" = "/usr/bin/ruby1.9.1"',
		user => root,
		require => Package['ruby1.9.1'],
	}

	exec { '/usr/bin/update-alternatives --set gem /usr/bin/gem1.9.1':
		unless => '/usr/bin/test "`/bin/readlink /etc/alternatives/gem`" = "/usr/bin/gem1.9.1"',
		user => root,
		require => [
			Package['ruby1.9.1'],
			Package['rubygems'],
		],
	}
}