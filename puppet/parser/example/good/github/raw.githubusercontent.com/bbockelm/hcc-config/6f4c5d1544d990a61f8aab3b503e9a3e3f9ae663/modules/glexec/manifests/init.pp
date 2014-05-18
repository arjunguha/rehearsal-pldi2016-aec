#
# Class: glexec
#

class glexec {

	include globus

	package { osg-wn-client-glexec: name => "osg-wn-client-glexec", ensure => installed, }

	file { "/etc/glexec.conf":
		owner   => "root", group => "glexec", mode => 640,
		ensure  => present,
		require => Package["osg-wn-client-glexec"],
		source  => "puppet:///modules/glexec/glexec.conf",
	}

}
