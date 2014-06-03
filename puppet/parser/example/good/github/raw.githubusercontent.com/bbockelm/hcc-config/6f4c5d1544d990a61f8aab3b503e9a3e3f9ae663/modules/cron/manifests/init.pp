#
# Class: cron
#

class cron {

	file { "cron.allow":
		path    => "/etc/cron.allow",
		owner   => "root", group => "root", mode => 644,
		content => inline_template(file("/etc/puppet/modules/cron/templates/cron.allow-$hostname.erb", "/etc/puppet/modules/cron/templates/cron.allow.erb")),
	}

}

