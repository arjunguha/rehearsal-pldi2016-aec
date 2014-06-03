# = Class: puppet::master
# vim: ts=2: sw=2
#
# == Description
#
# Used to facilitate source code distribution
#
class puppet::master inherits puppet {
	
	include puppet::client
		
	# One account is managed for each remote site
	# 
	# Each user should have a unique key
	puppet::master_rsync_user {
		ext1: ssh_public_key => 'ssh-rsa AAAAB3NzaC1yc2EAAAABIwAAAIEAylQ5YqQKkgJjjCPcsrzLg6xglpgKPYAhyx7M6IIaCclxlx2ayabpe5LlL4SmFsAvEMlYXFR1m4+90ltnyD7uK8IBiX8/6Nw+OfHpbI7kp7I68A6QzkPixF5dupZl0GrbCDGrbVQwemKB/d2L+EmgnU7Y0VM5qPbcj6XnsudaoqU= rsync_cronjob@REL';
		ext2: ssh_public_key => 'ssh-rsa AAAAB3NzaC1yc2EAAAABIwAAAIEAtvZwNUBxiebcNcXUcf+z++4rLDZXtHKSX3dva8Pk8kXe3R8JOmOSnDfKZ3spIMfrCoCp6ws9rwObwalmC7U8BwvLOPYXuXKgbYI9uRf1OzE5KswSQkFy2DUCG21BfuI43dBQQ17NsHoi845LAjZSfhyI6KCMYaGVNldBTISXXZE= rsync_cronjob@WBV';
	}

}

define puppet::master_rsync_user($ssh_public_key) {

	$user = "rsync${name}"

	# This uses the account module
	account::user { $user:
		ssh_public_keys => $ssh_public_key,
		groups => "rsync",
	}

}
