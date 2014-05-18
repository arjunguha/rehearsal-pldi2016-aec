# import site specific classes
# vim: ts=2: sw=2
#
import "../../sites/ex1/*.pp"

class ex1_role {
	include sudo
	include account::sysadmins
	include package_managers
	include resolver
	include puppet::client
}

class ex1_role_puppetmaster inherits ex1_role {
	include puppet::master
}

class ex1_role_puppetslave inherits ex1_role {
	include puppet::slave
}
