class role_red-worker57 {

	$isCondorWorker = true
	$mountsHDFS = true

	$gangliaClusterName = 'red-worker'
	$gangliaTCPAcceptChannel = '8651'
	$gangliaUDPSendChannel = [ 'red-mon.unl.edu', '8651' ]
	$gangliaUDPRecvChannel = '8651'

	$pakitiTag = "T2_US_Nebraska_Workers"
	$yum_extrarepo = [ 'epel', 'nebraska', 'osg' ]

   include general
   include users
   include pam
   include openssh
   include autofs
   include sudo
   include nrpe
   include hostcert
   include osg-ca-certs
   include fetch-crl
   include pakiti
   include ganglia
   
   include hadoop
   include condor
   include osg-wn-client
   include glexec
   include cvmfs

   # must hard mount OSGAPP and OSGDATA to make RSV probes happy
	# automounting will not show correct permissions
	file { "/opt/osg": ensure => directory }
	file { "/opt/osg/app": ensure => directory }
	mount { "/opt/osg/app":
		device  => "hcc-gridnfs:/osg/app",
		fstype  => "nfs4",
		ensure  => mounted,
		options => "rw,noatime,hard,intr,rsize=32768,wsize=32768",
		atboot  => true,
		require => [ File["/opt/osg"], File["/opt/osg/app"], ],
	}

	file { "/opt/osg/data": ensure => directory }
	mount { "/opt/osg/data":
		device  => "hcc-gridnfs:/osg/data",
		fstype  => "nfs4",
		ensure  => mounted,
		options => "rw,noatime,hard,intr,rsize=32768,wsize=32768",
		atboot  => true,
		require => [ File["/opt/osg"], File["/opt/osg/data"], ],
	}

	cron { "xfs_fsr":
		ensure => present,
		command => '/usr/sbin/xfs_fsr -t 72000',
		user => 'root',
		minute => '8',
		hour => '2',
	}
}
