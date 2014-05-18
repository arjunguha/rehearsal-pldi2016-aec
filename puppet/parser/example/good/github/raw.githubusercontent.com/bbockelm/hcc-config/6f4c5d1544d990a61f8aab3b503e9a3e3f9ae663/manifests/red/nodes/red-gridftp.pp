### red gridftp / xrootd servers

node /^red-gridftp\d+\.unl\.edu$/ inherits red-public {

	$yum_extrarepo = [ 'epel', 'nebraska', 'osg' ]
	$role = "red-gridftp"

	$sshExtraAdmins = [ 'jennyshao' ]
	$sudoExtraAdmins = [ 'jennyshao' ]

	include general
#	include nrpe

}

