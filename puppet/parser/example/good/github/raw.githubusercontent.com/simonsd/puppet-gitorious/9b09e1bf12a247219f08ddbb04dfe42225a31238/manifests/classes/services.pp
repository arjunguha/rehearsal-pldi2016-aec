class system::services {
    service { "sendmail":
        ensure => running,
        enable => true,
        hasstatus => true,
        hasrestart => true,
		name => $::operatingsystem ? {
			Centos => $::operatingsystemrelease ? {
				'6.0' => 'postfix',
				'*' => 'sendmail',
			},
			'*' => 'sendmail',
		},
    }  
}


class gitorious::services {

    file {
		"/etc/init.d/git-ultrasphinx":
			ensure => present,
			owner => "root",
			group => "root",
			mode => 755,
			content => template("gitorious/$::operatingsystem/git-ultrasphinx.erb");

		"/etc/init.d/git-daemon":
			ensure => present,
			owner => "root",
			group => "root",
			mode => 755,
			content => template("gitorious/$::operatingsystem/git-daemon.erb");
    }

	service {
		"git-ultrasphinx":
			ensure => running,
			enable => true,
			hasstatus => true,
			hasrestart => true,
			require => File["/etc/init.d/git-ultrasphinx"];

		"git-daemon":
			ensure => running,
			enable => true,
			hasstatus => true,
			hasrestart => true,
			require => File["/etc/init.d/git-daemon"];

		'iptables':
			ensure => stopped,
			enable => false;
	}

    exec {
		"stompserver start &":
			command => "stompserver start &",
			cwd => "/root/",
			require => Service["git-daemon"];

		"script/poller":
			environment => 'RAILS_ENV=production',
			command => "script/poller start",
			user => 'git',
			cwd => "${gitorious::home}",
			require => [Service["git-daemon"], File["${gitorious::home}/tmp/pids"]];
    }
}
