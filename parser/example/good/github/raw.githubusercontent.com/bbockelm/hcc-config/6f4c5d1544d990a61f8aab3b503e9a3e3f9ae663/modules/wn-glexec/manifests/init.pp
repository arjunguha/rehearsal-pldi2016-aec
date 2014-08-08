#
# Class: wn-glexec
#
# Maintains glexec configs
#
# does -not- restart/install, only config management for now
#
class wn-glexec {
   
   # build the directory Structure
   file { "/etc/glexec":
		ensure => "directory",
      owner => "root", group => "root", mode => 644,
   }
   file { "/etc/glexec/contrib" :
      ensure => "directory",
      owner => "root", group => "root", mode => 644,
   }

   file { "/etc/glexec/lcas" :
      ensure => "directory",
      owner => "root", group => "root", mode => 644,
   }

   file { "/etc/glexec/lcmaps" :
      ensure => "directory",
      owner => "root", group => "root", mode => 644,
   }

   file { "/etc/glexec/contrib/glexec_monitor" :
   	ensure => "directory",
		owner => "root", group => "root", mode => 644,	
   }

	file { "/etc/glexec/contrib/gums_interface" :
      ensure => "directory",
      owner => "root", group => "root", mode => 644,
   }




	# main glexec config
	file { "/etc/glexec/testglexec":
		ensure  => "present",
		owner   => "root", group => "root", mode => 644,
		source  => "puppet:///modules/wn-glexec/testglexec",
	}

	file { "/etc/glexec/glexec.conf":
      ensure  => "present",
      owner   => "root", group => "root", mode => 644,
      source  => "puppet:///modules/wn-glexec/glexec.conf",
   }
	file { "/etc/glexec/tracking_groups.cfg":
      ensure  => "present",
      owner   => "root", group => "root", mode => 644,
      source  => "puppet:///modules/wn-glexec/tracking_groups.cfg",
   }
   file { "/etc/glexec/contrib_monitor":
      ensure  => "present",
      owner   => "root", group => "root", mode => 644,
      source  => "puppet:///modules/wn-glexec/contrib_monitor",
   } 

	file { "/etc/glexec/lcas/ban_users.db":
      ensure  => "present",
      owner   => "root", group => "root", mode => 644,
      source  => "puppet:///modules/wn-glexec/lcas/ban_users.db",
   }

   file { "/etc/glexec/lcas/lcas-suexec.db":
      ensure  => "present",
      owner   => "root", group => "root", mode => 644,
      source  => "puppet:///modules/wn-glexec/lcas/lcas-suexec.db",
   }

	file { "/etc/glexec/lcmaps/lcmaps-suexec.db":
      ensure  => "present",
      owner   => "root", group => "root", mode => 644,
      source  => "puppet:///modules/wn-glexec/lcmaps/lcmaps-suexec.db",
   }
   
	file { "/etc/glexec/contrib/glexec_monitor/glexec_monitor.cfg":
      ensure  => "present",
      owner   => "root", group => "root", mode => 644,
      source  => "puppet:///modules/wn-glexec/contrib/glexec_monitor/glexec_monitor.cfg",
   }
   file { "/etc/glexec/contrib/gums_interface/getmapping.cfg":
      ensure  => "present",
      owner   => "root", group => "root", mode => 644,
      source  => "puppet:///modules/wn-glexec/contrib/gums_interface/getmapping.cfg",
   }
}

