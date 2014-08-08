class ack-grep ($user) {
	package { 'ack-grep':
		ensure => present,
	}

	appendLineToFile { 'Add ack to .bashrc':
		file => "/home/$user/.bashrc",
		line => 'alias ack=ack-grep',
		user => $user,

		require => Package['ack-grep'],
	}
}