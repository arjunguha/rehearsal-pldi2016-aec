#
# Class: at
#

class at {

	# at should be disabled by default, but keep it that way
	service { "atd":
		name       => "atd",
		ensure     => stopped,
		enable     => false,
		hasrestart => true,
		hasstatus  => true,
	}

	file { "at.allow":
		path    => "/etc/at.allow",
		owner   => "root", group => "root", mode => 600,
		content => template("at/at.allow.erb"),
	}

}

