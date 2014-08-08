# Class: lamp
#
# This module manages lamp
#
# Parameters:
#
# Actions:
#
# Requires:
#
# Sample Usage:
#
# [Remember: No empty lines between comments and class definition]
class lamp ($mysqlPassword = "dev", $pathToHostfile = "/vagrant/manifests/default") {

	# Set the default path for commands, saves a lot of extra typing down the line
	Exec {
		path => ["/usr/bin", "/bin", "/usr/sbin", "/sbin", "/usr/local/bin",
		"/usr/local/sbin"]
	}

	# Some standard requirements, like apt-get update
	include bootstrap

	# Build a LAMP with some tasty extra's
	# Based on https://github.com/whatsthatweb/vagrant-puppet-LAMP, but changed mysql and apache to a parameterized classes
	class { 'apache' :
            pathToHostfile => $pathToHostfile,
    	}
	include php
	include php::pear # Can also install codesniffer, phpunit, phing etc if you uncomment them
	include php::pecl # Also installs xdebug
	class { 'mysql' :
        mysqlPassword => $mysqlPassword,
	}
	include phpmyadmin
}
