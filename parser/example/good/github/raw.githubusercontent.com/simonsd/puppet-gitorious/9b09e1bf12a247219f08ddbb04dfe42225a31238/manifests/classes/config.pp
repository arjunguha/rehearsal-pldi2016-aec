class gitorious::config {
    file {
		"$gitorious::home/config/database.yml":
			content => template("gitorious/common/database.yml.erb"),
			ensure => present,
			owner => "git",
			group => "git";

		"$gitorious::home/config/gitorious.yml":
			content => template("gitorious/common/gitorious.yml.erb"),
			ensure => present,
			owner => "git",
			group => "git";

		"$gitorious::home/config/broker.yml":
			content => template("gitorious/common/broker.yml.erb"),
			ensure => present,
			owner => "git",
			group => "git";

		"$gitorious::home/config/environments/production.rb":
			content => template("gitorious/common/production.rb.erb"),
			ensure => present;

		"/etc/ld.so.conf.d/gitorious.conf":
			path => "/etc/ld.so.conf.d/gitorious.conf",
			content => template('gitorious/common/gitorious.conf.erb'),
			owner => "root",
			group => "root";

		"/etc/$gitorious::webserver/conf.d/gitorious.conf":
			content => template('gitorious/common/apache-gitorious.conf.erb'),
			owner => root,
			group => root,
			before => Service["$webserver"],
			mode => 0644;
	}

	exec {
		"migrate_db":
			environment => "RAILS_ENV=production",
			command => "bundle exec rake db:migrate",
			cwd => "/usr/share/gitorious/",
			require => File["$gitorious::home/config/environments/production.rb"];

		"bootstrap_sphinx":
			command => 'bundle exec rake ultrasphinx:bootstrap',
			environment => 'RAILS_ENV=production',
			cwd => "/usr/share/gitorious/",
			require => Exec["migrate_db"],
			notify => Service["httpd"];

		'gitorious_chown':
			command => 'chown -R git:git /usr/share/gitorious',
			refreshonly => true,
			subscribe => Exec['migrate_db'];

		"ldconfig":
			command => "ldconfig",
			cwd => "/root/",
			refreshonly => true,
			subscribe => [File["/etc/ld.so.conf.d/gitorious.conf"]];
	}
}
