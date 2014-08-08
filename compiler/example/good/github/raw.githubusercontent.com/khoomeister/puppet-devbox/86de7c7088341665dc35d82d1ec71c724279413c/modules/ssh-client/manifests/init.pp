class ssh-client ($user) {
	file { "/home/$user/.ssh":
		ensure => directory,
		mode => 700,
		owner => $user,
	}

	file { "/home/$user/.ssh/config":
		ensure => file,
		mode => 600,
		owner => $user,

		require => File["/home/$user/.ssh"]
	}

	appendLineToFile { 'Enable shared SSH connections':
		file => "/home/$user/.ssh/config",
		line => 'ControlMaster auto',
		user => $user,

		require => File["/home/$user/.ssh/config"],
	}

	appendLineToFile { 'Enable shared SSH connections (setting 2)':
		file => "/home/$user/.ssh/config",
		line => 'ControlPath /tmp/ssh_mux_%h_%p_%r',
		user => $user,

		require => File["/home/$user/.ssh/config"],
	}

	appendLineToFile { 'Persist SSH connections for faster reconnections':
		file => "/home/$user/.ssh/config",
		line => 'ControlPersist 4h',
		user => $user,

		require => File["/home/$user/.ssh/config"],
	}

	appendLineToFile { 'Disable GSSAPI authentication because it is slow':
		file => "/home/$user/.ssh/config",
		line => 'GSSAPIAuthentication no',
		user => $user,

		require => File["/home/$user/.ssh/config"],
	}
}
