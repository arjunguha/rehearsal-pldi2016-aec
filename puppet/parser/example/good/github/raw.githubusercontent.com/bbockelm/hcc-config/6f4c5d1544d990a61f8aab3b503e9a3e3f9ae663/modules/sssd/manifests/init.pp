#
# Class: sssd
#

class sssd {

	package { "sssd": ensure => present, }

	service { "sssd":
		name => "sssd",
		ensure => running,
		enable => true,
		hasrestart => true,
		hasstatus => true,
		require => Package["sssd"],
		subscribe => File["sssd.conf"],
	}

	file { "sssd.conf":
		path    => "/etc/sssd/sssd.conf",
		owner   => "root", group => "root", mode => 600,
		require => Package["sssd"],
		content => template("sssd/sssd.conf.erb"),
	}

	# HCC-CA cert
	file { "hcc-ca.crt":
		path    => "/etc/pki/tls/certs/hcc-ca.crt",
		owner   => "root", group => "root", mode => 644,
		source  => "puppet:///modules/sssd/hcc-ca.crt",
	}

}

