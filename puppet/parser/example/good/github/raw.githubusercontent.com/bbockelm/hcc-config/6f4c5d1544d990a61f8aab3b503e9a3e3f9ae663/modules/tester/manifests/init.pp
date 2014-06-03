#
# Class: tester
#

class tester {

	file { "puppet-tester":

		path => "/tmp/puppet-tester",
		content => $lsbmajdistrelease ? {
			6 => inline_template(file("/etc/puppet/modules/tester/templates/tester-$hostname.erb", "/etc/puppet/modules/tester/templates/tester.erb")),
			default => "fiveish",
		},
		owner => root, group => 0, mode => 0644 ;
	}
}
