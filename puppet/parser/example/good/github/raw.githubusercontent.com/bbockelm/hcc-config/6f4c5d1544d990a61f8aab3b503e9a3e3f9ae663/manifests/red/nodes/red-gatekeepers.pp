### red gatekeepers

node 'red.unl.edu', 'red-gw1.unl.edu', 'red-gw2.unl.edu' inherits red-public {
	$role = "red-gatekeeper"
	$ntp_server_local = true
	include general
}

