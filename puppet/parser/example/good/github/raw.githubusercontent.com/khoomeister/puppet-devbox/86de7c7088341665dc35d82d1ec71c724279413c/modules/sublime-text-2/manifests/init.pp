class sublime-text-2 ($user) {
	define dirandfile ($directory, $sourceUrl, $owner) {
		file { $directory:
			ensure => directory,
			owner => $owner,
		}

		file { "$directory/$name":
			ensure => file,
			owner => $owner,
			source => $sourceUrl,
			
			require => File[$directory],
		}
	}

	package { 'sublime-text-2-beta':
		ensure => present,
	}

	exec { '"/opt/Sublime Text 2/sublime_text" --command exit':
		creates => "/home/$user/.config/sublime-text-2",
		environment => [ "HOME=/home/$user", "USER=$user" ],
		user => $user,

		require => Package['sublime-text-2-beta'],
	}

	# setup Puppet code coloring
	dirandfile { 'Puppet.tmLanguage':
		directory => "/home/$user/.config/sublime-text-2/Packages/Puppet",
		sourceUrl => 'puppet:///modules/sublime-text-2/Puppet.tmLanguage',
		owner => $user,

		require => Exec['"/opt/Sublime Text 2/sublime_text" --command exit']
	}

	# setup CoffeeScript code coloring
	dirandfile { 'CoffeeScript.tmLanguage':
		directory => "/home/$user/.config/sublime-text-2/Packages/CoffeeScript",
		sourceUrl => 'puppet:///modules/sublime-text-2/CoffeeScript.tmLanguage',
		owner => $user,

		require => Exec['"/opt/Sublime Text 2/sublime_text" --command exit']
	}

	# setup keyboard shortcuts
	file { "/home/$user/.config/sublime-text-2/Packages/User/Default (Linux).sublime-keymap":
		ensure => file,
		owner => $user,
		source => 'puppet:///modules/sublime-text-2/Default (Linux).sublime-keymap',

		require => Exec['"/opt/Sublime Text 2/sublime_text" --command exit']
	}

	# setup font
	file { "/home/$user/.config/sublime-text-2/Packages/User/Base File.sublime-settings":
		ensure => file,
		owner => $user,
		source => 'puppet:///modules/sublime-text-2/Base File.sublime-settings',

		require => Exec['"/opt/Sublime Text 2/sublime_text" --command exit']
	}

	# create /usr/local/bin/sublime
	file { '/usr/local/bin/sublime':
		ensure => link,
		mode => 755,
		target => '/usr/bin/sublime-text-2',
		owner => root,
	}
}
