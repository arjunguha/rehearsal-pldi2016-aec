class sentry ($path, $host_name, $db_name, $db_username, $db_password) {
	$ve_path = "$path/ve"
	package { [
		"libpq-dev",
		"nginx",
		"postgresql",
		"python-dev",
		"python-virtualenv",
		"supervisor"
		]:
		ensure => installed,
		require => Exec["update_apt"]
	}
	exec {
		"update_apt":
			command => "/usr/bin/apt-get update";
		"create_db":
			command => "/usr/bin/psql -c \"CREATE USER $db_username WITH PASSWORD '$db_password'\" && /usr/bin/psql -c \"CREATE DATABASE $db_name\" && /usr/bin/psql -c \"GRANT ALL PRIVILEGES ON DATABASE $db_name TO $db_username\" && touch $path/db.created",
			user => "postgres",
			creates => "$path/db.created",
			require => [Exec["pip_install"], Package["postgresql"]];
		"create_path": 
			command => "/bin/mkdir -p $path",
			creates => "$path";
		"ve_init":
			command => "/usr/bin/virtualenv $ve_path",
			unless => "/usr/bin/test -d $ve_path",
			require => [Package['python-virtualenv'], Exec['create_path']];
		"pip_install":
			command => '/bin/sh -c ". ve/bin/activate && pip install -r requirements.pip && deactivate"',
			cwd => "$path",
			require => [Exec["ve_init"], File["requirements"], Package["libpq-dev", "postgresql", "python-dev"]];
	}
	file { 
		"requirements":
			path => "$path/requirements.pip",
			ensure => file,
			source => 'puppet:///modules/sentry/requirements.pip',
			require => Exec["create_path"];
		"$path/sentry_conf.py":
			ensure => file,
			content => template("sentry/sentry_conf.py"),
			notify => Service["supervisor"],
			require => Exec["create_path"];
		"/etc/nginx/sites-enabled/sentry.conf":
			ensure => file,
			content => template("sentry/nginx.conf"),
			notify => Service["nginx"],
			require => Package["nginx"];
		"/etc/supervisor/conf.d/sentry.conf":
			ensure => file,
			content => template("sentry/supervisor.conf"),
			require => Exec["create_db"],
			notify => Service["supervisor"],
	}
	service {
		"nginx":
			enable => "true",
			ensure => "running",
			require => Package["nginx"];
		"postgresql":
			enable => "true",
			ensure => "running",
			require => Package["postgresql"];
		"supervisor":
			enable => "true",
			ensure => "running",
			require => Package["supervisor"];
	}
}