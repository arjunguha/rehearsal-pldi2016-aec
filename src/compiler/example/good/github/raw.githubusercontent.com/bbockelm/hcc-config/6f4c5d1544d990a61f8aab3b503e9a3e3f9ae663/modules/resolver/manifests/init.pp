#
# Class: resolver
#
# Manages /etc/resolv.conf
#

class resolver {

	file { "resolv.conf":
		path    => "/etc/resolv.conf",
		mode    => 644,
		owner   => "root",
		group   => "root",
		ensure  => present,
		content => template("resolver/resolv.conf.erb"),
	}

}
