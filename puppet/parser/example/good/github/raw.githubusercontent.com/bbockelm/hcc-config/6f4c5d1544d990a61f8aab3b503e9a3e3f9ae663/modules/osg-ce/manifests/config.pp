class osg-ce::config {

	$require = Class["osg-ce::install"]

	file { "extattr_table.txt":
		ensure  => present,
		path    => "/etc/osg/extattr_table.txt",
		owner   => "root", group => "root", mode => '0644',
		source  => "puppet:///modules/osg-ce/extattr_table.txt",
	}

	file { "uid_table.txt":
		ensure  => present,
		path    => "/etc/osg/uid_table.txt",
		owner   => "root", group => "root", mode => '0644',
		source  => "puppet:///modules/osg-ce/uid_table.txt",
	}

#	file { "condor.pm":
#		ensure  => present,
#		path    => "/usr/lib/perl5/vendor_perl/5.8.8/Globus/GRAM/JobManager/condor.pm",
#		owner   => "root", group => "root", mode => '0644',
#		source  => "puppet:///modules/osg-ce/condor.pm",
#	}

   file { "globus-gatekeeper.logrotate":
      ensure => present,
      path   => "/etc/logrotate.d/globus-gatekeeper",
      owner  => "root", group => "root", mode => '0644',
      source => "puppet:///modules/osg-ce/globus-gatekeeper.logrotate",
   }

	file { "condor.pm":
		ensure  => present,
		path    => "/usr/share/perl5/vendor_perl/Globus/GRAM/JobManager/condor.pm",
		owner   => "root", group => "root", mode => '0644',
		source  => "puppet:///modules/osg-ce/condor.pm",
	}

	file { "/var/log/globus": ensure => directory, mode => '1777', }
	file { "/var/lib/globus/gram_scratch": ensure => directory, mode => '1777', }
	file { "/var/lib/globus/gass_cache": ensure => directory, mode => '1777', }
	file { "/var/lib/globus/gram_job_state": ensure => directory, mode => '1777', }
	file { "/var/lib/globus/job_home": ensure => directory, mode => '1777', }
	file { "globus-gram-job-manager.conf":
		ensure  => present,
		path    => "/etc/globus/globus-gram-job-manager.conf",
		owner   => "root", group => "root", mode => '0644',
		source  => "puppet:///modules/osg-ce/globus-gram-job-manager.conf",
	}

	# Override RVF entries so we can relocate jobs.
	file { "globus-gram-job-manager.rvf":
		ensure  => present,
		path    => "/usr/share/globus/globus_gram_job_manager/globus-gram-job-manager.rvf",
		owner   => "root", group => "root", mode => '0644',
		source  => "puppet:///modules/osg-ce/globus-gram-job-manager.rvf",
	}

   # globus-gram-job-manager 16.23 and later allow you to override the RVF from /etc
   # Once all the CEs are on that version, the above entry can go away.
   file { "/etc/globus/gram": ensure => directory, mode => '1755', owner=>"root", group =>"root" }
   file { "job-manager.rvf":
      ensure  => present,
      path    => "/etc/globus/gram/job-manager.rvf",
      owner   => "root", group => "root", mode => '0644',
      source  => "puppet:///modules/osg-ce/job-manager.rvf",
   }


	file { "ProbeConfig":
		ensure  => present,
		path    => "/etc/gratia/condor/ProbeConfig",
		owner   => "root", group => "root", mode => '0644',
		content => template("osg-ce/ProbeConfig.erb"),
	}

	file { "lcmaps.db":
		ensure  => present,
		path    => "/etc/lcmaps.db",
		owner   => "root", group => "root", mode => '0644',
		content => template("osg-ce/lcmaps.db.erb"),
	}

	file { "gsi-authz.conf":
		ensure  => present,
		path    => "/etc/grid-security/gsi-authz.conf",
		owner   => "root", group => "root", mode => '0644',
		source  => "puppet:///modules/osg-ce/gsi-authz.conf",
	}

	#######
	file { "gums-client.properties":
		ensure  => present,
		path    => "/etc/gums/gums-client.properties",
		owner   => "root", group => "root", mode => '0644',
		content => template("osg-ce/gums-client.properties.erb"),
	}

   # GIP upgrades currently break the permissions on these directories.
   # As of GIP 1.3.4; Feb 26, 2012; BB
	file { "/var/cache/gip":
      ensure => directory,
      owner => "tomcat", group => "tomcat", mode => "0644",
   }
   file { "/var/log/gip":
      ensure => directory,
      owner => "tomcat", group => "tomcat", mode => "0644",
	}

   # Customizations to advertise load-balanced gridftp server
	file { "add-attributes.conf":
		ensure	=> present,
		path		=> "/etc/gip/add-attributes.conf",
		owner		=>"root", group => "root", mode => "0644",
		content	=> template("osg-ce/add-attributes.conf.erb"),
	}

	# Custom authorizations for the Condor queues.
   file { "alter-attributes.conf":
      ensure   => present,
      path     => "/etc/gip/alter-attributes.conf",
      owner    =>"root", group => "root", mode => "0644",
      content  => template("osg-ce/alter-attributes.conf.erb"),
   }

	#######


	### /etc/osg/config.d/ settings ###
	file { "01-squid.ini":
		ensure  => present,
		path    => "/etc/osg/config.d/01-squid.ini",
		owner   => "root", group => "root", mode => '0644',
		content => template("osg-ce/config.d/01-squid.ini.erb"),
	}

	file { "10-misc.ini":
		ensure  => present,
		path    => "/etc/osg/config.d/10-misc.ini",
		owner   => "root", group => "root", mode => '0644',
		content => template("osg-ce/config.d/10-misc.ini.erb"),
	}

	file { "10-storage.ini":
		ensure  => present,
		path    => "/etc/osg/config.d/10-storage.ini",
		owner   => "root", group => "root", mode => '0644',
		content => template("osg-ce/config.d/10-storage.ini.erb"),
	}

	file { "15-managedfork.ini":
		ensure  => present,
		path    => "/etc/osg/config.d/15-managedfork.ini",
		owner   => "root", group => "root", mode => '0644',
		content => template("osg-ce/config.d/15-managedfork.ini.erb"),
	}

	file { "20-condor.ini":
		ensure  => present,
		path    => "/etc/osg/config.d/20-condor.ini",
		owner   => "root", group => "root", mode => '0644',
		content => template("osg-ce/config.d/20-condor.ini.erb"),
	}

	file { "30-cemon.ini":
		ensure  => present,
		path    => "/etc/osg/config.d/30-cemon.ini",
		owner   => "root", group => "root", mode => '0644',
		content => template("osg-ce/config.d/30-cemon.ini.erb"),
	}

	file { "30-gip.ini":
		ensure  => present,
		path    => "/etc/osg/config.d/30-gip.ini",
		owner   => "root", group => "root", mode => '0644',
		content => template("osg-ce/config.d/30-gip.ini.erb"),
	}

	file { "30-gratia.ini":
		ensure  => present,
		path    => "/etc/osg/config.d/30-gratia.ini",
		owner   => "root", group => "root", mode => '0644',
		content => template("osg-ce/config.d/30-gratia.ini.erb"),
	}

	file { "40-localsettings.ini":
		ensure  => present,
		path    => "/etc/osg/config.d/40-localsettings.ini",
		owner   => "root", group => "root", mode => '0644',
		content => template("osg-ce/config.d/40-localsettings.ini.erb"),
	}

	file { "40-siteinfo.ini":
		ensure  => present,
		path    => "/etc/osg/config.d/40-siteinfo.ini",
		owner   => "root", group => "root", mode => '0644',
		content => template("osg-ce/config.d/40-siteinfo.ini.erb"),
	}

   file { "sysctl.conf":
      ensure  => present,
      path    => "/etc/sysctl.conf",
      owner   => "root", group => "root", mode => '0644',
      source  => "puppet:///modules/osg-ce/sysctl.conf",
   }

   file { "globus-gatekeeper":
      ensure  => present,
      path    => "/etc/sysconfig/globus-gatekeeper",
      owner   => "root", group => "root", mode => '0644',
      source  => "puppet:///modules/osg-ce/globus-gatekeeper",
   }


	file { "osg-ce-httpcert.pem":
		path    => "/etc/grid-security/http/httpcert.pem",
		owner   => "tomcat", group => "tomcat", mode => 644,
		source  => "puppet:///hostcert/${hostname}-hostcert.pem",
	}

	file { "osg-ce-httpkey.pem":
		path    => "/etc/grid-security/http/httpkey.pem",
		owner   => "tomcat", group => "tomcat", mode => 600,
		source  => "puppet:///hostcert/${hostname}-hostkey.pem",
	}

}
