#
# Class: motd
#
# ... because we gots 'ta have ASCII
#

class motd {

	file { "/etc/motd":
		owner   => "root", group => "root", mode => 0644,
		source  => [ "puppet:///modules/motd/motd-$hostname", "puppet:///modules/motd/motd", ]
	}

}
