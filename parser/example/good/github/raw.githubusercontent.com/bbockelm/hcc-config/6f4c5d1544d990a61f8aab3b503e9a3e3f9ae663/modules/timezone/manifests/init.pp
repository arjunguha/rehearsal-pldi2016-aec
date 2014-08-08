#
# Class: timezone
#
# maintains the timezone
#

class timezone(
	$timezone_path = $timezone::params::timezone_path,
	$timezone_cmd = $timezone::params::timezone_cmd
) inherits timezone::params {

	file { 'timezone':
		path => $timezone_path,
		ensure => present,
		owner => 'root', group => 'root', mode => '0644',
		content => $operatingsystem ? {
			default => template("timezone/timezone-${operatingsystem}" ),
		},
		notify => Exec['set-timezone'],
	}

	exec { 'set-timezone':
		command => $timezone_cmd,
		require => File['timezone'],
		subscribe => File['timezone'],
		refreshonly => true,
	}

}
