class ubuntu-default-setup ($user, $runUpdate, $canonicalArchiveRepoUrl, $googleChromeRepoUrl, $ppaNodeJsRepoUrl, $ppaSublimeText2RepoUrl, $ubuntuArchiveRepoUrl, $virtualboxRepoUrl) {
	define addAptKey($email) {
		# $name refers to URL
		exec { "/usr/bin/wget -q -O - $name | /usr/bin/apt-key add -":
			unless => "/usr/bin/apt-key list | /bin/grep $email",
			user => root,

			before => Exec['apt-get update'],
		}
	}

	define addPpaKey() {
		# $name refers to signing key
		exec { "/usr/bin/apt-key adv --keyserver keyserver.ubuntu.com --recv-keys $name":
			unless => "/usr/bin/apt-key list | /bin/grep $name",
			user => root,

			before => Exec['apt-get update'],
		}
	}	

	appendLineToFile { 'add pup alias':
		file => "/home/$user/.bashrc",
		line => 'alias pup=\"sudo puppet apply /etc/puppet/manifests/site.pp\"',
		user => $user,
	}

	file { '/etc/sudoers':
		source => 'puppet:///modules/ubuntu-default-setup/sudoers',
		mode => 440,
		owner => root,
		group => root,
	}

	file { '/etc/apt/sources.list':
		content => template('ubuntu-default-setup/sources.list.erb'),
		mode => 644,
		owner => root,
		group => root,
	}

	# add apt keys in case user wants to install software (this is done in ubuntu-default-setup to avoid running apt-get update multiple times)
	addAptKey { 'https://dl-ssl.google.com/linux/linux_signing_key.pub':
		email => 'linux-packages-keymaster@google.com',
	}
	addAptKey { 'http://download.virtualbox.org/virtualbox/debian/oracle_vbox.asc':
		email => 'info@virtualbox.org',
	}

	addPpaKey { [
		'C7917B12', # chris lea's nodejs package
		'EEA14886', # webupd8team's sublime text 2 package
	]: }

	exec { 'apt-get update':
		command => $runUpdate ? {
			true => 'apt-get update',
			false => 'echo apt-get update not run due to runUpdate set to false',
		},
		path => [
			'/bin',
			'/usr/bin',
		],
		user => root,

		require => File['/etc/apt/sources.list'],
	}

	# install packages that aren't included in the base installation
	# note: wget is included in the base installation
	package {[
		'git',
		'curl',
	]:
		ensure => present,

		require => Exec['apt-get update'],
	}

	# remove unneeded packages
	package {[
		'aisleriot',
		'banshee',
		'evolution-common',
		'gbrainy',
		'gnome-mahjongg',
		'gnome-sudoku',
		'gnomine',
		'indicator-me',
		'indicator-messages',
		'libevolution',
		'thunderbird',
		'totem'
	]:
		ensure => absent,
	}
	
	# create global package directory
	file { '/opt':
		ensure => 'directory',
	}

	file { '/opt/packages':
		ensure => 'directory',

		require => File['/opt'],
	}
}

define appendLineToFile($file, $line, $user) {
	# $name can refer to anything
	exec { "echo \"\\n$line\" >> \"$file\"":
		path => '/bin',
		unless => "grep -Fx \"$line\" \"$file\"",
		user => $user,
	}
}

define gconf($type, $value, $user) {
	# $name refers to the key being modified
	exec { "gconftool-2 --config-source xml:readwrite:/home/$user/.gconf --set \"$name\" --type $type \"$value\"":
		path => '/usr/bin',
		unless => "test \"`gconftool-2 --config-source xml:readwrite:/home/$user/.gconf --get \"$name\"`\" = \"$value\"",
		user => $user,
	}
}

define installDebFile($package, $source) {
	# $name refers to the local filename to place in /opt/packages

	file { "/opt/packages/$name":
		source => $source,

		require => File['/opt/packages'],
	}

	package { $package:
		provider => dpkg,
		ensure   => present,
		source   => "/opt/packages/$name",

		require => [
			File["/opt/packages/$name"],
		],
	}
}

define untar($tarSource, $tarOptions, $tarFileName, $destDirectory, $owner) {
	# $name refers to the destination file or directory it creates
	file { "/opt/packages/$tarFileName":
		ensure => file,
		mode => 774,
		owner => root,
		source => $tarSource,

		require => File['/opt/packages'],
	}

	exec { "tar $tarOptions \"/opt/packages/$tarFileName\" -C \"$destDirectory\"":
		creates => $name,
		path => '/bin',
		user => root,

		require => File["/opt/packages/$tarFileName"],
	}

	file { $name:
		ensure => present,
		recurse => true,
		owner => $owner,

		require => Exec["tar $tarOptions \"/opt/packages/$tarFileName\" -C \"$destDirectory\""],
	}
}
