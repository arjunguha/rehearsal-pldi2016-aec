class ubuntu-desktop-setup ($user) {
	package { 'gnome-shell':
		ensure => present,
	}

	# turn off update manager because it's annoying when it pops up
	# credits to http://lifehacker.com/5295449/disable-ubuntus-annoying-update-manager-popup
	gconf { '/apps/update-notifier/auto_launch':
		type => 'boolean',
		value => 'false',
		user => $user,
	}

	# set nautilus defaults - list view, show backup files & show hidden files
	gconf { '/apps/nautilus/preferences/default_folder_viewer':
		type => 'string',
		value => 'list_view',
		user => $user,
	}

	gconf { '/desktop/gnome/file_views/show_backup_files':
		type => 'boolean',
		value => 'true',
		user => $user,
	}

	gconf { '/desktop/gnome/file_views/show_hidden_files':
		type => 'boolean',
		value => 'true',
		user => $user,
	}

	# TODO: refactor into gconf-list function
	exec { 'set Shift + keypad to work like Microsoft Windows':
		command => "gconftool-2 --config-source xml:readwrite:/home/$user/.gconf --set \"/desktop/gnome/peripherals/keyboard/kbd/options\" --type list --list-type string [\"compat	numpad:microsoft\"]",
		path => '/usr/bin',
		unless => "test \"`gconftool-2 --config-source xml:readwrite:/home/$user/.gconf --get \"/desktop/gnome/peripherals/keyboard/kbd/options\"`\" = [\"compat	numpad:microsoft\"]",
		user => $user,
	}
}