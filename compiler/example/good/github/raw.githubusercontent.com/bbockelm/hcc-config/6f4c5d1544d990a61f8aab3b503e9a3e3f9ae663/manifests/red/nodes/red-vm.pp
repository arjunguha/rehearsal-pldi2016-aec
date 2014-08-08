### red vm hosts

node /red-vm[1,2,3,4].red.hcc.unl.edu/ inherits red-private {
	$role = "red-vm"
	include general
	include nrpe

	mount { "/home":
		device  => "t3-nfs:/home",
		fstype  => "nfs4",
		ensure  => mounted,
		options => "rw,noatime,hard,intr,rsize=32768,wsize=32768",
		atboot  => true,
	}
}

node /red-vm[6,7,8].red.hcc.unl.edu/ inherits red-private {
	$role = "red-vm"
	include general

	mount { "/home":
		device  => "t3-nfs:/home",
		fstype  => "nfs4",
		ensure  => mounted,
		options => "rw,noatime,hard,intr,rsize=32768,wsize=32768",
		atboot  => true,
	}
}
