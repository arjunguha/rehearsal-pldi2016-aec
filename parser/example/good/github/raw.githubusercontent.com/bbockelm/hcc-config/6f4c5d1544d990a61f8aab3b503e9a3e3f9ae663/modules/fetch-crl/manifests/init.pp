#
# Class: fetch-crl
#
# manages fetch-crl
#
class fetch-crl {

	package { fetch-crl: name => "fetch-crl", ensure => present }

	service { "fetch-crl":
		name       => "fetch-crl-cron",
		ensure     => running,
		enable     => true,
		hasrestart => true,
		hasstatus  => true,
		require    => Package["fetch-crl"],
		subscribe  => File["fetch-crl.conf"],
	}

	file { "fetch-crl.conf":
		path    => "/etc/fetch-crl.conf",
		mode    => 644,
		owner   => "root",
		group   => "root",
		content => template("fetch-crl/fetch-crl.conf.erb"),
		require => Package[fetch-crl],
		ensure  => present,
	}

}
