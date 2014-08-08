class google-chrome {
	# To install stable, remove beta first (if it is present)
	package { 'google-chrome-beta':
		ensure => absent,
	}
		
	package { 'google-chrome-stable':
		ensure => present,
		require => Package['google-chrome-beta'],
	}
}