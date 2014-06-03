#
# Class: bestman
#

class bestman {

	include fetch-crl

	package { "bestman2-server":
		ensure => present,
	}

	service { "bestman2":
		name => "bestman2",
		ensure => running,
		enable => true,
		hasrestart => true,
		hasstatus => true,
		require => [ Package["bestman2-server"], File["sudo-bestman"], File["bestman-httpcert.pem"], File["bestman-httpkey.pem"], ],
		subscribe => [ File["bestman2.rc"], File["bestman-httpcert.pem"], File["bestman-httpkey.pem"], ],
	}

	file { "bestman2.rc":
		path    => "/etc/bestman2/conf/bestman2.rc",
		owner   => "root", group => "root", mode => 644,
		require => Package["bestman2-server"],
		content => template("bestman/bestman2.rc.erb"),
	}


	file { "sudo-bestman":
		path    => "/etc/sudoers.d/sudo-bestman",
		owner   => "root", group => "root", mode => 0440,
		require => Class["sudo"],
		source  => "puppet:///modules/bestman/sudo-bestman",
	}


	# custom http certs for bestman -- grab from puppetmaster directly since
	# some things require /etc/grid-security/http/http* to be owned strangely
	# (this is in contrast to how the hostcert module does it)

	### FIXME: why does bestman require host and not http cert to function?

	file { "bestman-httpcert.pem":
		path    => "/etc/grid-security/http/bestman-httpcert.pem",
		owner   => "bestman", group => "bestman", mode => 644,
		source  => "puppet:///hostcert/${hostname}-hostcert.pem",
	}

	file { "bestman-httpkey.pem":
		path    => "/etc/grid-security/http/bestman-httpkey.pem",
		owner   => "bestman", group => "bestman", mode => 600,
		source  => "puppet:///hostcert/${hostname}-hostkey.pem",
	}

}

