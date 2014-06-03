#
# Class: pakiti
#

class pakiti {

	package { pakiti-client:
		ensure => present,
		require => Class["osg-ca-certs"],
	 }

	file { "/etc/pakiti2/pakiti2-client.conf":
		owner   => "root", group => "root", mode => 0640,
		content => template("pakiti/pakiti2-client.conf.erb"),
		require => Package["pakiti-client"],
	}

}
