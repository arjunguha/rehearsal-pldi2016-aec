#
# Class: osg-ce
#
class osg-ce {

	include osg-ce::params, osg-ce::install, osg-ce::config, osg-ce::service

	# must hard mount OSGAPP and OSGDATA to make RSV probes happy
	# automounting will not show correct permissions
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
    file { "cic-functions.sh":
      path    => "/opt/osg/app/etc/cic-functions.sh",
      source  => "puppet:///modules/osg-ce/cic-functions.sh",
      mode    => "0644", owner => "cmssoft", group => "grid",
      ensure  => present,
      require => File["/opt/osg/app"],
   }
	file {"gip_updater.sh":
		path	=> "/opt/osg/app/etc//gip_updater.sh",
	   source => "puppet:///modules/osg-ce/gip_updater.sh",
      mode   => "0774", owner => "cmssoft", group => "grid",
	   ensure => present,
	}

	file {"gip_updater.cron":
		path	=> "/etc/cron.d/gip_updater.cron",
	   source => "puppet:///modules/osg-ce/gip_updater.cron",
      mode   => "0644", owner => "root", group => "root",
	   ensure => present,
	}
}
