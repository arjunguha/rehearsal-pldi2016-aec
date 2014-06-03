class git-settings ($fullName, $email, $user) {
	define gituserconfig($user, $value) {
		exec { "/usr/bin/git config -f /home/$user/.gitconfig $name \"$value\"":
			unless => "/usr/bin/test \"`git config -f /home/$user/.gitconfig --get $name`\" = \"$value\"",
			user => $user,

			require => Package['git'],
		}
	}

	gituserconfig { 'color.ui':
		user => $user,
		value => 'auto',
	}
	
	gituserconfig { 'user.name':
		user => $user,
		value => $fullName,
	}

	gituserconfig { 'user.email':
		user => $user,
		value => $email,
	}

	exec { '/usr/bin/git config --system http.postBuffer "52428800"':
		unless => '/usr/bin/test "`git config --system --get http.postBuffer`" = "52428800"',
		user => root,

		require => Package['git'],
	}
}
