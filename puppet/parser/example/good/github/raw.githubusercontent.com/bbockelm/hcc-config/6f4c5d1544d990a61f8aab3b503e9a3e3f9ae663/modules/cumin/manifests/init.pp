#
# Class: cumin
#
# Maintains the cumin service
#
# does -not- restart/install, only config management for now
#
# After initial install, start postgresql and run:
# cumin-database install
# 
# To add a new user, run:
# cumin-admin add-user $USERNAME

class cumin {

	include hostcert

	package { cumin: name => "cumin", ensure => installed }
   # Appears to be a missing dep for cumin.
	package { python-qpid: name => "python-qpid", ensure => installed }
   package { qpid-cpp-server: name => "qpid-cpp-server.x86_64", ensure => installed }

   service { "cumin":
      name => "cumin",
      enable => false,
      hasrestart => true,
      hasstatus => true,
      require => [ Package["cumin"], Class["hostcert"] ],
   }

   service { "postgresql":
      name => "postgresql",
      enable => true,
      hasrestart => true,
      hasstatus => true,
      require => [ Package["cumin"], Class["hostcert"] ],
   }

   service { "qpidd":
      name => "qpidd",
      enable => false,
      hasrestart => true,
      hasstatus => true,
      require => [ Package["cumin"], Class["hostcert"] ],
   }  

	file { "/etc/cumin/cumin.conf":
		owner   => "root", group => "root", mode => "0600",
		ensure  => present,
		source  => "puppet:///modules/cumin/cumin.conf",
		require => Package["cumin"],
	}

   file { "/etc/qpidd.conf":
      owner   => "root", group => "root", mode => "0644",
      ensure  => present,
      source  => "puppet:///modules/cumin/qpidd.conf",
      require => Package["qpid-cpp-server"],
   }

   file { "/etc/qpid/qpidd.acl":
      owner   => "root", group => "root", mode => "0600",
      ensure  => present,
      source  => "puppet:///modules/cumin/qpidd.acl",
      require => Package["qpid-cpp-server"],
   }

## NOTE: /var/lib/qpidd/qpidd.sasl is not sync'd using puppet.
## This is because I don't know if /etc/puppet is "secure" for exporting
## secrets.

## NOTE: Similar story for /etc/cumin/cumin.crt and /etc/cumin/cumin.key

}

