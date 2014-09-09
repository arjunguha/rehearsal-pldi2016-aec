class gitolite ($user) {
	package { gitolite:
		ensure => present,
	}

	exec { "/usr/bin/ssh-keygen -q -t rsa -f \"/home/$user/.ssh/id_rsa\" -N \"\"":
		creates => "/home/$user/.ssh/id_rsa.pub",
		user => $user,
	}

	exec { "/usr/bin/ssh-agent ssh-add \"/home/$user/.ssh/id_rsa\"":
		user => $user,

		require => Exec["/usr/bin/ssh-keygen -q -t rsa -f \"/home/$user/.ssh/id_rsa\" -N \"\""],
	}

	file { "/tmp/$user.pub":
		source => "/home/$user/.ssh/id_rsa.pub",

		require => Exec["/usr/bin/ssh-keygen -q -t rsa -f \"/home/$user/.ssh/id_rsa\" -N \"\""],
	}

	exec { "/usr/bin/gl-setup /tmp/$user.pub":
		creates => '/var/lib/gitolite/repositories/gitolite-admin.git',
		environment => [ "HOME=/var/lib/gitolite", "USER=gitolite" ],
		user => gitolite,

		require => [
			File["/tmp/$user.pub"],
			Package['gitolite'],
		],
	}

	exec { "/usr/bin/ssh-keyscan localhost > /home/$user/.ssh/known_hosts":
		creates => "/home/$user/.ssh/known_hosts",
		user => $user,

		require => Package['gitolite'],
	}

	exec { '/usr/bin/git clone gitolite@localhost:gitolite-admin':
		creates => "/home/$user/gitolite-admin",
		environment => [ "HOME=/home/$user", "USER=$user" ],
		cwd => "/home/$user",
		user => $user,

		require => [
			Exec["/usr/bin/gl-setup /tmp/$user.pub"],
			Exec["/usr/bin/ssh-agent ssh-add \"/home/$user/.ssh/id_rsa\""],
			Exec["/usr/bin/ssh-keyscan localhost > /home/$user/.ssh/known_hosts"],
		],
	}

	/*
	To add a repo:
	1. sublime ~/gitolite-admin/conf/gitolite.conf.
	2. Add the line "repo <repoName>" followed by the lines specifying permissions.
	3. Save file, exit, git add, commit & push.

	To add users & set permissions:
	1. Ensure each .pub file is named <username>.pub.
	2. Copy the pub files to ~/gitolite-admin/keydir
	3. sublime ~/gitolite-admin/conf/gitolite.conf
	4. Give the new users permissions as required.
	2. Save file, exit, git add, commit & push.

	More information about how to specify permissions are at http://sitaramc.github.com/gitolite/doc/gitolite.conf.html

	Credit: http://www.silassewell.com/blog/2011/01/08/setup-gitolite-on-ubuntu/
	*/
}