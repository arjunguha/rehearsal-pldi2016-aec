class redmine::config {
	file {
		'database.yml':
			ensure => present,
			owner => $apache::user,
			group => $apache::group,
			path => $::operatingsystem ? {
				default => '/usr/share/redmine/config/database.yml',
				Debian => '/etc/redmine/default/database.yml',
			},
			content => template("redmine/database.yml.erb");

		'configuration.yml':
			ensure => present,
			owner => $apache::user,
			group => $apache::group,
			path => "$redmine::home/config/configuration.yml",
			content => template('redmine/configuration.yml.erb');
	}

	exec {
		'chown redmine':
			command => "chown -R ${apache::user}:${apache::group} ${redmine::home}",
			provider => shell;
	}

	vhost {
		'redmine':
			documentroot => "${redmine::home}/public",
			insecure => no,
			ssl => on,
			servername => "${redmine::servername}",
			serveralias => "${redmine::serveralias}";
	}

	exec {
		'session_store':
			path => '/opt/ruby1.8/bin:/bin:/usr/bin',
			cwd => '/usr/share/redmine/public',
			provider => 'shell',
			command => 'rake generate_session_store',
			require => [ Package['gem_rails'], Vhost['redmine'] ];
	}
}
