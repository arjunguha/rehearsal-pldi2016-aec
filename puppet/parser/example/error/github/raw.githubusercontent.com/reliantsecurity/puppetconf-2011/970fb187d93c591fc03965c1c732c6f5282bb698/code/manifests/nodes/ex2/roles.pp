# import site specific classes
# vim: ts=2: sw=2
#
import "../../sites/ex2/*.pp"

class ex2_role {
	include sudo
	include account::sysadmins
	include package_managers
	include resolver
	include puppet::client
}

class ex2_role_puppetmaster inherits ex2_role {
	include puppet::master
}

class ex2_role_puppetslave inherits ex2_role {
	include puppet::slave
}
