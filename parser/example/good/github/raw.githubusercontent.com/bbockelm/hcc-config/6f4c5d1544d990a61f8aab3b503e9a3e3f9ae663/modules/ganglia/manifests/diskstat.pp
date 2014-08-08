#
# Class: ganglia::diskstat
#
# manages ganglia diskstat plugin
#
class ganglia::diskstat {

	file { "diskstat.pyconf":
		path    => "/etc/ganglia/conf.d/diskstat.pyconf",
		mode    => 644,
		owner   => "root",
		group   => "root",
		content => template("ganglia/conf.d/diskstat.pyconf"),
		require => Package[ganglia-gmond-modules-python],
		ensure  => present,
		notify  => Service[gmond],
	}

	file { "diskstat.py":
		path    => "/usr/lib64/ganglia/python_modules/diskstat.py",
		mode    => 644,
		owner   => "root",
		group   => "root",
		source  => "puppet:///modules/ganglia/python_modules/diskstat.py",
		require => Package[ganglia-gmond-modules-python],
		ensure  => present,
	}

}
