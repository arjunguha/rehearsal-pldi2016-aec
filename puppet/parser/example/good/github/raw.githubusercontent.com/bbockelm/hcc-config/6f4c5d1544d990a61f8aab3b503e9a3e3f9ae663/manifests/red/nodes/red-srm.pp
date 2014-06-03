### red bestman servers

node 'srm.unl.edu' inherits red-public {
	$role = "red-srm"
	include general
	include nrpe
	include xrootd
}

node 'red-srm1.unl.edu', 'dcache07.unl.edu' inherits red-public {
	$role = "red-srm"
	include general
	include nrpe
}

node 'red-srm2.unl.edu' inherits red-public {
	include general
}

