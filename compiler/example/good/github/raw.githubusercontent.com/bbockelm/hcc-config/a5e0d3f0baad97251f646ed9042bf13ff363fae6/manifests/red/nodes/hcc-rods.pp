node 'hcc-rods.unl.edu' inherits red-public {

	$sshExtraAdmins = [ 'acaprez', 'jwang', 'dweitzel', 'bbockelm' ]
	$sudoExtraAdmins = [ 'acaprez', 'tharvill', 'jsamuels', 'jwang', 'dweitzel', 'bbockelm' ]

	$mountsHDFS = true

	include general

	include hadoop
   include ganglia

}

