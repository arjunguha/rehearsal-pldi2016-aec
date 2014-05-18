#
# Class: ganglia::temperatures
#
# manages ganglia temperatures plugin
#
class ganglia::temperatures {

	package { "ganglia-gmond-modules-python":
		name => "ganglia-gmond-modules-python",
		ensure => present,
	}

	package { "OpenIPMI-tools":
		name => "OpenIPMI-tools",
		ensure => present,
	}

	file { "temperatures.pyconf":
		path    => "/etc/ganglia/conf.d/temperatures.pyconf",
		mode    => 644,
		owner   => "root",
		group   => "root",
		content => template("ganglia/conf.d/temperatures.pyconf"),
		require => Package[ganglia-gmond-modules-python],
		ensure  => present,
		notify  => Service[gmond],
	}

	file { "temperatures.py":
		path    => "/usr/lib64/ganglia/python_modules/temperatures.py",
		mode    => 644,
		owner   => "root",
		group   => "root",
		source  => "puppet://$servername/ganglia/python_modules/temperatures.py",
		require => Package[ganglia-gmond-modules-python],
		ensure  => present,
	}

}
