class role_red-worker-el6 {

	$isCondorWorker = true
	$condorCustom09 = "el6"
   $mountsHDFS = true

	$gangliaClusterName = 'red-worker'
	$gangliaTCPAcceptChannel = '8651'
	$gangliaUDPSendChannel = [ 'red-mon.unl.edu', '8651' ]
	$gangliaUDPRecvChannel = '8651'

	include condor
	include ganglia
	include fetch-crl
   include osg-wn-client
   include glexec
   include cvmfs
#	include chroot
   include osg-ca-certs
   include hadoop
   include cgroups
   include nrpe
   include sudo
   include updatedb
	include selinuxmodules

	chroot::root { 'sl6':
		version => 1,
		yum => 'puppet:///common/yum-sl6.conf',
		rpms => 'acl attr bind-utils cyrus-sasl-plain lsof libcgroup quota rhel-instnum cpuspeed dos2unix m2crypto sssd nc prctl setarch tree unix2dos unzip wget zip zlib glibc-devel perl-Compress-Zlib',
		rpms_suid => 'osg-wn-client glexec lcmaps-plugins-condor-update lcmaps-plugins-process-tracking lcmaps-plugins-mount-under-scratch',
	}

	mount { "/home":
		device  => "t3-nfs:/export/home",
		fstype  => "nfs",
		ensure  => mounted,
		options => "nfsvers=3,rw,noatime,hard,intr,rsize=32768,wsize=32768",
		atboot  => true,
	}



	###########################
	### CVMFS static mounts ###
	###########################

	file { '/chroot/sl6-v1/root/cvmfs':
		ensure => directory,
		owner => 'root', group => 'root', mode => '0755',
		backup => false,
	}
	file { '/chroot/sl6-v1/root/cvmfs/cms.cern.ch':
		ensure => directory,
		backup => false,
	}
	mount { '/chroot/sl6-v1/root/cvmfs/cms.cern.ch':
		device => 'cms.cern.ch',
		fstype => 'cvmfs',
		ensure => mounted,
		options => 'defaults',
		remounts => false,
		atboot => true,
		require => File['/chroot/sl6-v1/root/cvmfs/cms.cern.ch'],
	}

	file { '/chroot/sl6-v1/root/cvmfs/oasis.opensciencegrid.org':
		ensure => directory,
		backup => false,
	}
	mount { '/chroot/sl6-v1/root/cvmfs/oasis.opensciencegrid.org':
		device => 'oasis.opensciencegrid.org',
		fstype => 'cvmfs',
		ensure => mounted,
		options => 'defaults',
		remounts => false,
		atboot => true,
		require => File['/chroot/sl6-v1/root/cvmfs/oasis.opensciencegrid.org'],
	}

	file { '/cvmfs':
		ensure => directory,
		owner => 'root', group => 'root', mode => '0755',
		backup => false,
	}
	file { '/cvmfs/cms.cern.ch':
		ensure => link,
		target => '/chroot/sl6-v1/root/cvmfs/cms.cern.ch',
		backup => false,
	}
	file { '/cvmfs/oasis.opensciencegrid.org':
		ensure => link,
		target => '/chroot/sl6-v1/root/cvmfs/oasis.opensciencegrid.org',
		backup => false,
	}


	# legacy /opt/osg/app/cmssoft/cms -> /cvmfs/cms.cern.ch symlink
	file { '/opt/osg':
		ensure => directory,
		backup => false,
	}
	file { '/opt/osg/app':
		ensure => directory,
		backup => false,
	}
	file { '/opt/osg/app/cmssoft':
		ensure => directory,
		backup => false,
	}
	file { '/opt/osg/app/cmssoft/cms':
		ensure => link,
		target => '/cvmfs/cms.cern.ch',
		backup => false,
	}



	# disable transparent huge pages for now, kernel bug of some kind
	exec { "disable_thp":
		command => 'echo never > /sys/kernel/mm/redhat_transparent_hugepage/enabled',
		unless => 'grep "\[never\]" /sys/kernel/mm/redhat_transparent_hugepage/enabled',
	}

}
