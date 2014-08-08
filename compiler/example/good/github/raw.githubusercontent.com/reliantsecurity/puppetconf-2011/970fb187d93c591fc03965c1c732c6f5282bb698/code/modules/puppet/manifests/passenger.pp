# = Class: puppet::passenger
#
# == Description
# Provides passenger
class puppet::passenger {

	include ruby
	include packages
	Package <| title == passenger |> { require => Class[ruby] }
	
	tools::gem_cleanup { passenger: subscribe => Package[passenger] }

	# Each supported client OS goes here
	case $operatingsystem {
		solaris: { include puppet::passenger::solaris }
		debian: { include puppet::passenger::debian }
	}

}
