### red infrastructure nodes (single nodes, groups go in their own .pp file)

node 'hcc-mon.unl.edu' inherits red-public {
	include general
}

node 'hcc-schorr-ns1.unl.edu' inherits red-public {
	$yum_extrarepo = [ 'epel', 'hcc', ]
    include general
    include ganglia
    include nrpe
}

node 'hcc-cvmfs.unl.edu' inherits red-public {
    $sshExtraAdmins = [ 'dykstra' ]
    $sudoExtraAdmins = [ 'dykstra' ]
	$yum_extrarepo = [ 'epel', 'hcc', 'osg', ]
    include general
    include ganglia
    include nrpe
}

node 'hcc-class.unl.edu' inherits red-public {
    $sshExtraAdmins = [ 'acaprez', 'dswanson' ]
    $sudoExtraAdmins = [ 'acaprez', 'dswanson' ]
	$yum_extrarepo = [ 'epel', 'hcc', 'osg', ]
    include general
    include ganglia
    include nrpe
}

node 'phedex.unl.edu' inherits red-public {
	$mountsHDFS = true
   $isPHEDEX = true   
	$sshExtraAdmins = [ 'barrefors', ]
	$sudoExtraAdmins = [ 'barrefors', ]
	include general
	include ganglia
	include hadoop
	include nrpe
}

node 'phedex-new.unl.edu' inherits red-public {
	$mountsHDFS = true
   $isPHEDEX = true   
	$sshExtraAdmins = [ 'barrefors', ]
	$sudoExtraAdmins = [ 'barrefors', ]
	include general
	include ganglia
	include hadoop
	include nrpe
}
node 'brian-test.unl.edu' inherits red-public {
	$mountsHDFS = true
	include general
	include ganglia
	include hadoop
	include nrpe
}

node 'hcc-derek.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'dweitzel' ]
	$sudoExtraAdmins = [ 'dweitzel' ]
	$mountsHDFS = true
	include general
	include ganglia
	include hadoop
	include nrpe
}

node 'hcc-ganglia.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'acaprez', 'zzhang' ]
	$sudoExtraAdmins = [ 'acaprez', ]
	$yum_extrarepo = [ 'epel', 'hcc', 'nginx' ]
	include general
	include yum
}

node 'red-net1.unl.edu', 'red-net2.unl.edu' inherits red-private {
	include general
	include ganglia
}

node 'hcc-crabserver.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'belforte', 'letts', 'spadhi', 'crab', 'lolass' ]
	$sudoExtraAdmins = [ 'belforte', 'letts', 'crab', 'lolass' ]
	$users_ldap_servers = [ 'red-ldap1.unl.edu', 'red-ldap2.unl.edu' ]
    $gangliaClusterName = 'crab-infrastructure'
    $gangliaUDPSendChannel = [ 'red-mon.unl.edu', '8652' ]

	include general

	mount { "/home":
		device  => "t3-nfs:/home",
		fstype  => "nfs4",
		ensure  => mounted,
		options => "rw,noatime,hard,intr,rsize=32768,wsize=32768",
		atboot  => true,
	}
}

node 'hcc-factoryv3.unl.edu', 'hcc-frontendv3.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'acaprez', 'dweitzel' ]
	$sudoExtraAdmins = [ 'acaprez', 'dweitzel' ]
	include general
   include hostcert
   include osg-ca-certs
   include fetch-crl

	mount { "/home":
		device  => "t3-nfs:/home",
		fstype  => "nfs4",
		ensure  => mounted,
		options => "rw,noatime,hard,intr,rsize=32768,wsize=32768",
		atboot  => true,
	}
}

node 'hcc-uniquant.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'acaprez', 'dweitzel' ]
	$sudoExtraAdmins = [ 'acaprez', 'dweitzel' ]

	include general

	mount { "/home":
		device  => "t3-nfs:/home",
		fstype  => "nfs4",
		ensure  => mounted,
		options => "rw,noatime,hard,intr,rsize=32768,wsize=32768",
		atboot  => true,
	}
}

node 'red-web.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'acaprez', 'jwang', 'dweitzel', 'bbockelm' ]
	$sudoExtraAdmins = [ 'acaprez', 'tharvill', 'jsamuels', 'jwang', 'dweitzel', 'bbockelm' ]
	include general
}

node 'red-dir1.unl.edu', 'red-dir2.unl.edu' inherits red-public {
	include general
	include ganglia
	include nrpe
	include lvs
}

node 'red-squid1.unl.edu', 'red-squid2.unl.edu' inherits red-public {
	include general
	include ganglia
	include nrpe
}

node 'hcc-voms.unl.edu' inherits red-public {
	include general
	include ganglia
	include nrpe
}

node 'red-condor.unl.edu' inherits red-public {
	$isCondorCollector = true
	$role = "red-collector"
	include general
	include ganglia
	include nrpe
}

node 'red-mon.unl.edu' inherits red-public {

	$sshExtraAdmins = [ 'dweitzel', 'acaprez', ]
	$sudoExtraAdmins = [ 'dweitzel', 'acaprez', ]
   $pakitiTag = "T2_US_Nebraska"
	$yum_extrarepo = [ 'epel', 'hcc', 'osg' ]

	include general

}

node 'xrootd.unl.edu' inherits red-public {
	$mountsHDFS = true
	include general
	include xrootd
}

node 'xrootd-itb.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'zzhang', 'barrefors', ]
	$sudoExtraAdmins = [ 'zzhang', 'barrefors', ]
	$mountsHDFS = true
	include general
}

node 'glidein.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'acaprez', 'jwang', 'dweitzel', 'bbockelm' ]
	$sudoExtraAdmins = [ 'acaprez', 'tharvill', 'jsamuels', 'jwang', 'dweitzel', 'bbockelm' ]
	$pakitiTag = "T2_US_Nebraska"
	# general discluded intentionally
	include hosts
}

node 'hcc-gridnfs.red.hcc.unl.edu' inherits red-private {
	include general
}

node 't2.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'acaprez', 'jwang', 'dweitzel', 'bbockelm', 'git' ]
	$sudoExtraAdmins = [ 'acaprez', 'tharvill', 'jsamuels', 'jwang', 'dweitzel', 'bbockelm' ]

	include general
}

node 't3-nfs.red.hcc.unl.edu' inherits red-private {

	include general
	include hadoop
	include nfs::server

	# t3 home storage is mounted on /export so link to allow local logins
	# have to use force to remove /home dir if it exists already
	file { '/home': ensure => link, target => '/export/home', force => true, }

	ssh_authorized_key { "red-dump":
		ensure => "present",
		type => "ssh-dss",
      key => "AAAAB3NzaC1kc3MAAACBAKLkTzJmk4ms4xmZO1CobLWKSKn2mxLPHOI8+YQJeP0DfY9GkB40UAhJleSaFiYl4SVx1VcNhWRawpxT1triUF/6ddDTsQ6itsjjuHKGq87QfMwrnNAaMp3bPf7d3BOz3t4xSugy/YsOMtT50NzTMTFkXV+D/K+S+R/SqSIi4BSTAAAAFQDmjYIT9eSZRvlJ1MXobgyyLauqywAAAIB6V0PfanakhNbNlCMyec5ClASa5Agy/PmByBzho5zPXlLozBD7/5WTLCGIECAkCruQFChtSs7Rzg9AMOhRsxzGq4QXs7JD6Pums7PQi9gZnjSTYyKHAEIp/veOQVKP7MEtxgkumdXIHaeob5L/dclY6Y+1R6nfGqN3NLprxvpUQwAAAIBaQl72b7R96XyHxgoxgfkV+s+8Uwb7zU1pWSylEsCjFKpVcwub+IcUSkpU42XYj2lGqyCGC2jeut3lBOEu29ZAJvrOP67QeZKdaO5ybhJObI+3NNdvMMLkfCxU3HdWjcUz8JoRgRyUJyeLg05q3jQciNvfuuJx2AlF9+pikDRnGg==",
#		options => 'from="red-dump,172.16.200.1"',
		user => "root",
	}
}

node 't3.unl.edu' inherits red-public {
	$sudoExtraAdmins = [ 'acaprez', ]
	$mountsHDFS = true
	$isCondorSubmitter = true
   $ntp_server_local = true
   $yum_extrarepo = [ 'epel', 'hcc','osg' ]

	# ldap override so users can change password
	$users_ldap_servers = [ "hcc-ldap01.unl.edu", "hcc-ldap04.unl.edu" ]

	include general

	include condor
	include hadoop

	include cvmfs

	# OSGAPP and OSGDATA hard mounted to keep users sane
	file { "/opt/osg": ensure => directory }
	file { "/opt/osg/app": ensure => directory, require => File["/opt/osg"], }
	mount { "/opt/osg/app":
		device  => "hcc-gridnfs:/osg/app",
		fstype  => "nfs4",
		ensure  => absent,
		options => "rw,noatime,hard,intr,rsize=32768,wsize=32768",
		atboot  => true,
		require => File["/opt/osg/app"],
	}

	file { "/opt/osg/data": ensure => directory, require => File["/opt/osg"], }
	mount { "/opt/osg/data":
		device  => "hcc-gridnfs:/osg/data",
		fstype  => "nfs4",
		ensure  => absent,
		options => "rw,noatime,hard,intr,rsize=32768,wsize=32768",
		atboot  => true,
		require => File["/opt/osg/data"],
	}

	mount { "/home":
		device  => "t3-nfs:/home",
		fstype  => "nfs4",
		ensure  => mounted,
		options => "rw,noatime,hard,intr,rsize=32768,wsize=32768",
		atboot  => true,
	}
}

node 'red-ldap1.unl.edu', 'red-ldap2.unl.edu' inherits red-public {
	include general
	include nrpe
}

node 'red-auth.unl.edu' inherits red-public {
	include general
	include nrpe
	include osg-ca-certs
}

node 'red-fdt.unl.edu' inherits red-public {
	$isFDT = true
	$sshExtraAdmins = [ 'zdenek' ]
   $sudoExtraAdmins = [ 'zdenek' ]
	include general
}

node 'hcc-cache1.unl.edu', 'hcc-cache2.unl.edu' inherits red-public {
	include general
}

node 'hadoop-name.red.hcc.unl.edu' inherits red-private {
	$isHDFSname = true
	include general
	include nrpe
	include hadoop
}

node 'hadoop-tracker.red.hcc.unl.edu' inherits red-private {
	include general
	include nrpe
	include hadoop

	mount { "/mnt/fsimage":
		device  => "t3-nfs:/fsimage",
		fstype  => "nfs4",
		ensure  => mounted,
		options => "rw,noatime,hard,intr,rsize=32768,wsize=32768",
		atboot  => true,
	}
}

node 'rcf-gratia.unl.edu' inherits red-public {

	$sshExtraAdmins = [ 'acaprez', 'jwang', 'dweitzel', 'bbockelm', 'wbhurst' ]
	$sudoExtraAdmins = [ 'acaprez', 'tharvill', 'jsamuels', 'jwang', 'dweitzel', 'bbockelm', 'wbhurst' ]

	include general
	include ganglia

	mount { "/home":
		device  => "t3-nfs:/home",
		fstype  => "nfs4",
		ensure  => mounted,
		options => "rw,noatime,hard,intr,rsize=32768,wsize=32768",
		atboot  => true,
	}

}

node 'hcc-lsf.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'dweitzel' ]
	$sudoExtraAdmins = [ 'dweitzel' ]
	include general
	include ganglia
}

node 'hcc-andrew.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'akoerner', 'bjacobitz' ]
	$sudoExtraAdmins = [ 'akoerner' ]
	include general
	include ganglia
}

node 'hcc-jenny.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'jennyshao' ]
	$sudoExtraAdmins = [ 'jennyshao' ]
	include general
	include ganglia
}

node 'hcc-marian.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'zvada' ]
	$sudoExtraAdmins = [ 'zvada' ]
	include general
	include ganglia
}

node 'hcc-jingchao.unl.edu', 'hcc-jingchao2.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'jingchao', 'gattebur' ]
	$sudoExtraAdmins = [ 'jingchao' ]
	include general
	include ganglia
}

node 'hcc-web.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'acaprez' ]
	$sudoExtraAdmins = [ 'acaprez' ]
	include general
	include ganglia
}

node 'hcc-kartik.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'kartik' ]
	$sudoExtraAdmins = [ 'kartik' ]
	include general
	include ganglia
}

node 'hcc-bjorn.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'barrefors' ]
	$sudoExtraAdmins = [ 'barrefors' ]
	include general
	include ganglia
}

node 'hcc-scavenger.unl.edu' inherits red-public {
	$sshExtraAdmins = [ 'dweitzel' ]
	$sudoExtraAdmins = [ 'dweitzel' ]
	include general
	include ganglia
}
