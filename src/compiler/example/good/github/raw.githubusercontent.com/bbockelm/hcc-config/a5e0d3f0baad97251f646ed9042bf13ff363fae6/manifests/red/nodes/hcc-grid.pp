
node 'pf-grid.unl.edu' inherits red-public {

	$sshExtraAdmins = [ 'acaprez', 'jwang', 'dweitzel', 'bbockelm' ]
	$sudoExtraAdmins = [ 'acaprez', 'tharvill', 'jsamuels', 'jwang', 'dweitzel', 'bbockelm' ]

	include general
	include nrpe
   include ganglia
#	include condor
#	include osg-ce

   # Condor-CE
   class { 'osg_ce_condor':
      gums_server => 'red-auth.unl.edu',
      rms         => 'condor-ce-condor',
      rms_config  => 'puppet:///modules/osg_ce_condor/02-ce-pf.conf',
   }

}


