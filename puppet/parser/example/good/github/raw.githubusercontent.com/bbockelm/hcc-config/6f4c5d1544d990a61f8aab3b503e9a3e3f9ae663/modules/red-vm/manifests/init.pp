#
# Class: red-vm
#
class red-vm {

	package { [ "cman", "libvirt", "qemu-kvm", "qemu-kvm-tools", "lvm2-cluster", "python-virtinst", "virt-viewer", "virt-manager", "iscsi-initiator-utils", "syslinux", ]:
		ensure => present,
	}

	file { "iscsid.conf":
		ensure => present,
		path => "/etc/iscsi/iscsid.conf",
		mode => "0644", owner => "root", group => "root",
		source => [ "puppet:///modules/red-vm/iscsid.conf-$hostname", "puppet:///modules/red-vm/iscsid.conf", ],
	}

	file { "multipath.conf":
		ensure => present,
		path => "/etc/multipath.conf",
		mode => "0644", owner => "root", group => "root",
		source => [ "puppet:///modules/red-vm/multipath.conf-$hostname", "puppet:///modules/red-vm/multipath.conf", ],
	}

	file { "lvm.conf":
		ensure => present,
		path => "/etc/lvm/lvm.conf",
		mode => "0644", owner => "root", group => "root",
		source => [ "puppet:///modules/red-vm/lvm.conf-$hostname", "puppet:///modules/red-vm/lvm.conf", ],
	}

	service { "multipathd":
		ensure => running,
		enable => true,
		hasrestart => true,
		hasstatus => true,
		require => File["multipath.conf"],
		subscribe => File["multipath.conf"],
	}

	# no iscsid here, better to do that manually

}
