
# storage nodes in rm17

node /^red-stor\d+\.red\.hcc\.unl\.edu$/ inherits red-public {

	$yum_extrarepo = [ 'epel', 'nebraska', 'osg' ]
	$role = "red-stor"

	include general

}
