class syncftp {
	package { lftp:
		ensure => present,
	}

	file { '/usr/local/bin/syncftp':
		ensure => file,
		group => root,
		mode => 755,
		owner => root,
		source => 'puppet:///modules/syncftp/syncftp',

		require => Package['lftp'],
	}
}