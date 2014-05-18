class role_red-gatekeeper {

	$isCondorSubmitter = true
	$mountsHDFS = true

	include nrpe
   include ganglia
	include condor
	include osg-ce
	include cvmfs


	###########################
	### CVMFS static mounts ###
	###########################

	file { '/cvmfs':
		ensure => directory,
		owner => 'root', group => 'root', mode => '0755',
	}
	file { '/cvmfs/cms.cern.ch':
		ensure => directory,
	}
	mount { '/cvmfs/cms.cern.ch':
		device => 'cms.cern.ch',
		fstype => 'cvmfs',
		ensure => mounted,
		options => 'defaults',
		remounts => false,
		atboot => true,
		require => File['/cvmfs/cms.cern.ch'],
	}

	file { '/cvmfs/oasis.opensciencegrid.org':
		ensure => directory,
	}
	mount { '/cvmfs/oasis.opensciencegrid.org':
		device => 'oasis.opensciencegrid.org',
		fstype => 'cvmfs',
		ensure => mounted,
		options => 'defaults',
		remounts => false,
		atboot => true,
		require => File['/cvmfs/oasis.opensciencegrid.org'],
	}

}
