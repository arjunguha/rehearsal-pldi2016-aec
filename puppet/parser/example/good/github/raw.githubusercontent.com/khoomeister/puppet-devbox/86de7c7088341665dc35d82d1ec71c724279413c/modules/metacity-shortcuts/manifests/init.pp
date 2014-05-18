class metacity-shortcuts ($switchWindowXOffset = false, $user) {
	gconf { '/apps/metacity/global_keybindings/panel_run_dialog':
		type => 'string',
		value => '<Super>space',
		user => $user,
	}

	if $switchWindowXOffset {
		package { wmctrl:
			ensure => present,
		}

		file { '/usr/local/bin/switch-active-window':
			content => template('metacity-shortcuts/switch-active-window.erb'),
			group => root,
			mode => 755,
			owner => root,
		}

		gconf { '/apps/metacity/global_keybindings/run_command_12':
			type => 'string',
			value => '<Super>s',
			user => $user,

			require => File ['/usr/local/bin/switch-active-window'],
		}

		gconf { '/apps/metacity/keybinding_commands/command_12':
			type => 'string',
			value => 'switch-active-window',
			user => $user,

			require => File ['/usr/local/bin/switch-active-window'],
		}

		# credits
		# http://ubuntuforums.org/showthread.php?t=1414155 for the solution (but changed to using wmctrl)
		# https://bbs.archlinux.org/viewtopic.php?id=32328 for grep -a
	}
}