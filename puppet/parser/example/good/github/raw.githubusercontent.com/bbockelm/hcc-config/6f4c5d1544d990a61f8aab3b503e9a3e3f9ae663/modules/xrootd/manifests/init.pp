#
# Class: xrootd
#

class xrootd {

	include fetch-crl
	include hadoop
	include hostcert

	package { "xrootd-server.x86_64":
		ensure => present,
	}

	package { "xrootd-hdfs.x86_64":
		ensure => present,
		require => Package["xrootd-server.x86_64"],
	}

	package { "xrootd-lcmaps.x86_64":
		ensure => present,
		require => Package["xrootd-server.x86_64"],
	}

	package { "xrootd-cmstfc.x86_64":
		require => Package["xrootd-server.x86_64"],
		ensure => present,
	}

#	package { "xrootd-status-probe":
#		require => Package["nrpe"],
#		require => Class["nrpe"],
#		ensure => present,
#	}

	service { "xrootd":
		name => "xrootd",
		ensure => running,
		enable => true,
		hasrestart => true,
		hasstatus => true,
		require => [ Package["xrootd-server.x86_64"], File["xrdcert"], File["xrdkey"], Class["hadoop"], ],
		subscribe => File["xrootd-clustered.cfg"],
	}

	service { "cmsd":
		name => "cmsd",
		ensure => running,
		enable => true,
		hasrestart => true,
		hasstatus => true,
		require => [ Package["xrootd-server.x86_64"], File["xrdcert"], File["xrdkey"], Class["hadoop"], ],
		subscribe => [File["xrootd-clustered.cfg"], File["storage.xml"], File["lcmaps.cfg"], File["Authfile"]],
	}

	file { "xrootd-hdfs":
		path    => "/etc/sysconfig/xrootd-hdfs",
		owner   => "root", group => "root", mode => 644,
      require => Package["xrootd-server.x86_64"],
      source  => "puppet:///modules/xrootd/xrootd-hdfs",
   }

	file { "xrootd-clustered.cfg":
		path    => "/etc/xrootd/xrootd-clustered.cfg",
		owner   => "root", group => "root", mode => 644,
		require => Package["xrootd-server.x86_64"],
		content => inline_template(file("/etc/puppet/modules/xrootd/templates/xrootd-clustered-$hostname.cfg.erb", "/etc/puppet/modules/xrootd/templates/xrootd-clustered.cfg.erb")),
	}

	file { "storage.xml":
		path    => "/etc/xrootd/storage.xml",
		owner   => "root", group => "root", mode => 644,
		require => Package["xrootd-cmstfc.x86_64"],
		source  => "puppet:///modules/xrootd/storage.xml",
	}

	file { "lcmaps.cfg":
		path    => "/etc/xrootd/lcmaps.cfg",
		owner   => "root", group => "root", mode => 644,
		require => Package["xrootd-lcmaps.x86_64"],
		content => template("xrootd/lcmaps.cfg.erb"),
	}

	file { "Authfile":
		path    => "/etc/xrootd/Authfile",
		owner   => "root", group => "root", mode => 644,
		require => Package["xrootd-server.x86_64"],
		source  => "puppet:///modules/xrootd/Authfile",
	}

	# xrootd certificates are just a copy of hostcerts owned by xrootd:xrootd
	file { "xrd":
		path => "/etc/grid-security/xrd",
		ensure => directory,
		owner   => "xrootd", group => "xrootd", mode => 0755,
		require => Package["xrootd-server.x86_64"],
	}

	file { "xrdcert":
		path  => "/etc/grid-security/xrd/xrdcert.pem",
		owner => "xrootd", group => "xrootd", mode => 0644,
		source => "/etc/grid-security/hostcert.pem",
		require => Class["hostcert"],
	}

	file { "xrdkey":
		path  => "/etc/grid-security/xrd/xrdkey.pem",
		owner => "xrootd", group => "xrootd", mode => 0400,
		source => "/etc/grid-security/hostkey.pem",
		require => Class["hostcert"],
	}

}

