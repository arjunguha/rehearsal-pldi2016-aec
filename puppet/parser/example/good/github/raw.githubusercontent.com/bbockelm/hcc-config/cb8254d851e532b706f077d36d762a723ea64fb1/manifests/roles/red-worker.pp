class role_red-worker {

	$isCondorWorker = true

	$gangliaClusterName = 'red-worker'
	$gangliaTCPAcceptChannel = '8651'
	$gangliaUDPSendChannel = [ 'red-mon.unl.edu', '8651' ]
	$gangliaUDPRecvChannel = '8651'
	$yum_extrarepo = [ 'epel', 'hcc', 'osg' ]

	include condor
	include ganglia
#	include cgroups
	include fetch-crl
#  include wn-glexec

}
