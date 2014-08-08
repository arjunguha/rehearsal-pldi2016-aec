#
# Class: nfs
#

class nfs::server {

	include nfs

	service { "nfs":
		ensure     => running,
		enable     => true,
		hasrestart => true,
		hasstatus  => true,
		require    => Package["nfs-utils"],
		subscribe  => File["/etc/sysconfig/nfs"],
	}

	file { "/etc/sysconfig/nfs":
		owner   => "root", group => "root", mode => 0644,
		source  => "puppet:///modules/nfs/sysconfig-nfs-$hostname",
	}

	file { "/etc/exports":
		owner   => "root", group => "root", mode => 0644,
		source  => "puppet:///modules/nfs/exports-$hostname",
	}

}
