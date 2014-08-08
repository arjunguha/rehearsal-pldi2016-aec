# = Class puppet::passenger::solaris
#
# == Description
#
# A work-around for passenger versions 2.x on Solaris
class puppet::passenger::solaris {

	include puppet::passenger

	file { time-system-split-hpp:
		path => inline_template("<%= rubysitedir %>/../../gems/1.8/gems/passenger-${my_passenger_version}/ext/boost/date_time/time_system_split.hpp"),
		ensure => $my_passenger_version ? {
			/^2/ => present,
			default => undef,
		},
		replace => true,
		owner => 'root', 
		group => 'root', 
		mode => 0644,
		source => 'puppet:///modules/passenger/global/time_system_split.hpp',
		require => Package[passenger],
	}

}
