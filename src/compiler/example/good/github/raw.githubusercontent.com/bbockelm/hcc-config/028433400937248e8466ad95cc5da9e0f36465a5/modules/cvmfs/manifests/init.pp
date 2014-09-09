#
# Class: cvmfs
#
# manages install and configuration of CVMFS
#
class cvmfs {

   include cvmfs::params
   include autofs

	package { "cvmfs":
		name    => "${cvmfs::params::cvmfs_package_name}",
		ensure  => latest,
      require => User["cvmfs"],
      notify  => Service["autofs"],
	}

   package { "cvmfs-keys":
      name    => "cvmfs-keys",
      ensure  => present,
      require => Package["cvmfs"],
   }

   package { "fuse":
      name    => "fuse.x86_64",
      ensure  => present,
   }

	# we run cvmfs as a dedicated user
	group { "cvmfs":
		name => "${cvmfs::params::cvmfs_group}",
		ensure => present,
		system => true,
	}

	user { "cvmfs":
		name => "${cvmfs::params::cvmfs_user}",
		ensure => present,
		system => true,
		gid => "${cvmfs::params::cvmfs_group}",
      groups => ["${cvmfs::params::cvmfs_group}", "fuse"],
		require => [Group["cvmfs"], Package["fuse"]],
		managehome => false,
		shell => '/sbin/nologin',
	}

## Run daily fsck
##
   file { '/etc/cron.daily/cvmfs_fsck_all':
      mode    => "0755",
      owner   => "root",
      group   => "root",
      source  => "puppet:///modules/cvmfs/cvmfs_fsck_all",
      ensure  => present,
      require => Package["cvmfs"],
   }

## Files for talking to UW's CVMFS.
##
   file { "wisc_pubkey":
      path    => "/etc/cvmfs/keys/cms.hep.wisc.edu.pub",
      mode    => "0644",
      owner   => "root",
      group   => "root",
      source  => "puppet:///modules/cvmfs/cms.hep.wisc.edu.pub",
      ensure  => present,
      require => Package["cvmfs"],
   }

   file { "wisc_conf":
      path    => "/etc/cvmfs/config.d/cms.hep.wisc.edu.conf",
      mode    => "0644",
      owner   => "root",
      group   => "root",
      source  => "puppet:///modules/cvmfs/cms.hep.wisc.edu.conf",
      ensure  => present,
      require => Package["cvmfs"],
   }

## Files for talking to OSG's CVMFS.
##
   file { "osg_pubkey":
      path    => "/etc/cvmfs/keys/oasis.opensciencegrid.org.pub",
      mode    => "0644",
      owner   => "root",
      group   => "root",
      source  => "puppet:///modules/cvmfs/oasis.opensciencegrid.org.pub",
      ensure  => present,
      require => Package["cvmfs"],
   }

   file { "osg_conf":
      path    => "/etc/cvmfs/config.d/oasis.opensciencegrid.org.conf",
      mode    => "0644",
      owner   => "root",
      group   => "root",
      source  => "puppet:///modules/cvmfs/oasis.opensciencegrid.org.conf",
      ensure  => present,
      require => Package["cvmfs"],
   }

	file { "default.local":
		path    => "${cvmfs::params::cvmfs_config_file}",
		mode    => "0644",
		owner   => "root",
		group   => "root",
		source  => "puppet:///modules/cvmfs/default.local",
		require => Package["cvmfs"],
		ensure  => present,
	}

### Files for talking to CERN Belle
# FIXME: Should edit domain.d/cern.ch to only include mirrors that host all
#        CVMFS repos, then create config.d/cms.cern.ch.conf with additional
#        mirror URLs.
   file { "/etc/cvmfs/config.d/belle.cern.ch.conf":
      mode    => "0644",
      owner   => "root",
      group   => "root",
      source  => "puppet:///modules/cvmfs/belle.cern.ch.conf",
      ensure  => present,
      require => Package["cvmfs"],
   }

## Files for making CMS CVMFS work.
##
   file { "SITECONF_dir":
      path    => "/etc/cvmfs/SITECONF",
      mode    => "0644", owner => "root", group => "root",
      recurse => true,
      ensure  => directory,
      require => Package["cvmfs"],
   }

   file { "JobConfig_dir":
      path    => "/etc/cvmfs/SITECONF/JobConfig",
      mode    => "0644", owner => "root", group => "root",
      recurse => true,
      ensure  => directory,
      require => File["SITECONF_dir"],
   }

   file { "site-local-config.xml":
      path    => "/etc/cvmfs/SITECONF/JobConfig/site-local-config.xml",
      source  => "puppet:///modules/cvmfs/site-local-config.xml",
      mode    => "0644", owner => "root", group => "root",
      ensure  => present,
      require => File["JobConfig_dir"],
   }

   file { "PhEDEx_dir":
      path    => "/etc/cvmfs/SITECONF/PhEDEx",
      mode    => "0644", owner => "root", group => "root",
      recurse => true,
      ensure  => directory,
      require => File["SITECONF_dir"],
   }

   file { "PhEDEx_storage.xml":
      path    => "/etc/cvmfs/SITECONF/PhEDEx/storage.xml",
      source  => "puppet:///modules/cvmfs/PhEDEx_storage.xml",
      mode    => "0644", owner => "root", group => "root",
      ensure  => present,
      require => File["PhEDEx_dir"],
   }

## Use FNAL stratum one
##
   file { "FNAL_stratum_one":
      path    => "/etc/cvmfs/domain.d/cern.ch.local",
      source  => "puppet:///modules/cvmfs/cern.ch.local",
      mode    => "0644", owner => "root", group => "root",
      ensure  => present,
      require => Package["cvmfs"],
   }

   file { "fuse.conf":
      path    => "/etc/fuse.conf",
      mode    => "0644",
      owner   => "root",
      group   => "root",
      source  => "puppet:///modules/cvmfs/fuse.conf",
      ensure  => present,
   }

   file { "cvmfs_cache":
      path    => "/var/cache/cvmfs2",
      ensure  => directory,
      owner   => "cvmfs",
      group   => "cvmfs",
      mode    => 0700,
      require => [User["cvmfs"], Group["cvmfs"], Package["cvmfs"]],
   }

#	service { "cvmfs":
#		name       => "${cvmfs::params::cvmfs_service_name}",
#		ensure     => running,
#		enable     => true,
#		hasrestart => true,
#		hasstatus  => true,
#		require    => [Package["cvmfs"], File["default.local"], File["fuse.conf"], File["cvmfs_cache"]],
#		subscribe  => File["${cvmfs::params::cvmfs_config_file}"],
#	}

}

