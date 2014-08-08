class redshift ($lat, $lon, $user) {
	package { gtk-redshift:
		ensure => present,
	}

	file { "/home/$user/.config/redshift.conf":
		content => template('redshift/redshift.conf.erb'),
		mode => 644,
		owner => $user,
	}

	file { "/home/$user/.config/autostart":
		ensure => directory,
		mode => 755,
		owner => $user,
	}

	file { "/home/$user/.config/autostart/gtk-redshift.desktop":
		ensure => link,
		mode => 644,
		owner => $user,
		target => '/usr/share/applications/gtk-redshift.desktop',

		require => [
			Package['gtk-redshift'],
			File["/home/$user/.config/autostart"],
			File["/home/$user/.config/redshift.conf"],
		],
	}
}