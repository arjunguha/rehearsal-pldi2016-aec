class yum::prerequisites {

	package { "yum-priorities":
		name => $yum::params::packagename_yumpriority,
		ensure => present,
	}


	# purge any unmanaged repos
	file { 'yum_repos_d':
		path => '/etc/yum.repos.d/',
		ensure => directory,
		recurse => true,
		purge => true,
		force => true,
		require => Package[yum-priorities],
		owner => 'root',
		group => 'root',
		mode => '0755',
	}

}
