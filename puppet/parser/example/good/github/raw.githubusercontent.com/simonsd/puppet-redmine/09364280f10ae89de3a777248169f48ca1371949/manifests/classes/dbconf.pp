class redmine::dbconf {
	exec {
		'config_redmine_mysql_bootstrap':
			environment => 'RAILS_ENV=production',
			path => "$ruby::bin_dir",
			cwd => "$redmine::home",
			provider => shell,
			command => 'rake db:migrate',
			require => Mysql_db[$redmine::production_db],
			notify => Service["$apache::apache"];
		'load_default_data':
			environment => ['RAILS_ENV=production', 'REDMINE_LANG=en'],
			path => "$ruby::bin_dir",
			cwd => "$redmine::home",
			provider => 'shell',
			command => 'rake redmine:load_default_data',
			require => [ Mysql_db[$redmine::production_db], Exec['config_redmine_mysql_bootstrap'] ],
			notify => Service["$apache::apache"];
	}
}
