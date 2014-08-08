#
# Class: sudo
#

class sudo {

	package { sudo: ensure => present }

	file { "/etc/sudoers":
		owner   => "root", group => "root", mode => 0440,
		require => Package["sudo"],
		content => $lsbmajdistrelease ? {
			6 => template("sudo/sudoers-rhel6.erb"),
			default => template("sudo/sudoers.erb"),
		}
	}

	if $isFDT {
		file {"/etc/sudoers.d/sudo-fdt":
		ensure =>present,
		owner => "root", group => "root", mode => "0440",
		source => "puppet:///modules/sudo/sudo-fdt",
		require => File["/etc/sudoers.d"],
	}}

	if $isPHEDEX {
		file {"/etc/sudoers.d/sudo-phedex":
		ensure =>present,
		owner => "root", group => "root", mode => "0440",
		source => "puppet:///modules/sudo/sudo-phedex",
		require => File["/etc/sudoers.d"],
	}
}


	file { "/etc/sudoers.d":
		ensure => directory,
		owner  => "root", group => "root", mode => 0750,
	}

	file { "/etc/sudoers.d/sudo-admins":
		ensure  => present,
		owner   => "root", group => "root", mode => "0440",
		content => template("sudo/sudo-admins.erb"),
		require => File["/etc/sudoers.d"],
	}

}
