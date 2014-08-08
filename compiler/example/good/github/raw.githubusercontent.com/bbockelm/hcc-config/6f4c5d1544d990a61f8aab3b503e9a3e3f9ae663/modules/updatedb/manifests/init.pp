
#
# Class: updatedb
#
# Manages the updatedb configuration to prevent it from crawling Hadoop
#

class updatedb {

	file { "/etc/updatedb.conf":
		owner => "root", group => "root", mode => 0644,
		source => "puppet:///modules/updatedb/updatedb.conf",
	}

}

