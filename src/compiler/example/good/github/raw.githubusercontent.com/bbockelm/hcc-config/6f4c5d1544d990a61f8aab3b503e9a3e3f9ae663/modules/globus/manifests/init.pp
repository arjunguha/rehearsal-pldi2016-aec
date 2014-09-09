#
# Class: globus
#
# Misc globus configuration
#	- lcmaps.db
#	- gsiauthz.conf
#

class globus {

	package { "lcmaps.x86_64": ensure => latest, }
	package { "lcmaps-plugins-condor-update.x86_64": ensure => latest,  }
	package { "lcmaps-plugins-process-tracking.x86_64": ensure => latest,  }
   package { "lcmaps-plugins-mount-under-scratch.x86_64": ensure => latest, }

	file { "lcmaps.db":
		path    => "/etc/lcmaps.db",
		owner   => "root", group => "root", mode => 644,
		require => [Package["lcmaps.x86_64"],
          Package["lcmaps-plugins-mount-under-scratch.x86_64"],
          Package["lcmaps-plugins-condor-update.x86_64"],
          Package["lcmaps-plugins-process-tracking.x86_64"]],
		content => template("globus/lcmaps.db.erb"),
	}

	file { "gsi-authz.conf":
		path   => "/etc/grid-security/gsi-authz.conf",
		owner  => "root", group => "root", mode => 644,
		source => "puppet:///modules/globus/gsi-authz.conf",
	}

}

