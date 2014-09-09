#
# general baseline class for all nodes
#

class general {

	# minimal things needed to run puppet
	include minimal

	# only things that EVERYTHING should use go here
	include ntp
	include timezone
	include at
	include cron

   include users
   include pam
   include openssh
   include sudo
   include autofs
	include idmapd

	# role specific classes are included here
	if ( $role ) { include "role_$role" }

	include ganglia


	stage { "pre": before => Stage["main"] }
	class {
		"yum": stage => pre ;
		"yum::prerequisites": stage => pre ;
#		"yum::repo::nebraska":	stage => pre ;
#		"yum::repo::epel":	stage => pre ;
#		"yum::repo::osg":	stage => pre ;
	}


	# include testing classes if $testing = "yes"
	if ( $testing == "yes" ) { include "testing" }


	service { "yum":
		ensure => stopped,
		enable => false,
	}

	package { [ "htop", "dstat", "sysstat", "nmap", "strace", "gdb", "screen", "iotop" ]:
		ensure => present,
	}

	service { "cups": ensure => stopped, enable => false, }
	service { "avahi-daemon": ensure => stopped, enable => false, }

}
