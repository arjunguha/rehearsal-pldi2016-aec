# Class: hosts
#
# This class maintains /etc/hosts
#

class hosts {

	file { "hosts":
		ensure  => present,
		owner   => "root",
		group   => "root",
		mode    => 644,
		path    => "/etc/hosts",
		content => template("hosts/hosts.erb"),
	}

	if $::my_project { include "hosts::${my_project}" }

} # class hosts
