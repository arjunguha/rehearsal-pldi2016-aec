
class yum::repo::osg {

	# OSG gpg key
	# version = 824b8603
	# release = 4e726d80

	file { "RPM-GPG-KEY-OSG":
		path => '/etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
		source => "puppet:///modules/yum/rpm-gpg/RPM-GPG-KEY-OSG",
		ensure => present,
		owner => 'root', group => 'root', mode => '0644',
	}

	yum::managed_yumrepo {

		'osg':
			descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - \$basearch",
#			mirrorlist => "http://repo.grid.iu.edu/mirror/osg/3.1/el$lsbmajdistrelease/osg-release/\$basearch",
			baseurl => "http://t2.unl.edu/osg/3.1/el$lsbmajdistrelease/release/\$basearch",
			enabled => 1,
		 	gpgcheck => 1,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
			failovermethod => 'priority',
			priority => 98,
			require => File['RPM-GPG-KEY-OSG'] ;

		'osg-source':
			descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - \$basearch - Source",
	#		baseurl => "http://repo.grid.iu.edu/osg/3.1/el$lsbmajdistrelease/osg-release/source/SRPMS",
			baseurl => "http://t2.unl.edu/osg/osg/3.1/el$lsbmajdistrelease/release/source/SRPMS",
			enabled => 0,
	 		gpgcheck => 1,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
			failovermethod => 'priority',
			priority => 98,
			require => File['RPM-GPG-KEY-OSG'] ;

		'osg-debug':
			descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - \$basearch - Debug",
	#		baseurl => "http://repo.grid.iu.edu/osg/3.1/el$lsbmajdistrelease/release/\$basearch/debug",
			baseurl => "http://t2.unl.edu/osg/osg/3.1/el$lsbmajdistrelease/release/\$basearch/debug",
			enabled => 0,
	 		gpgcheck => 1,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
			failovermethod => 'priority',
			priority => 98,
			require => File['RPM-GPG-KEY-OSG'] ;

		'osg-upcoming':
			descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Upcoming - \$basearch",
#			mirrorlist => "http://repo.grid.iu.edu/mirror/osg/3.1/el$lsbmajdistrelease/osg-upcoming-release/\$basearch",
			baseurl => "http://t2.unl.edu/osg/upcoming/el$lsbmajdistrelease/release/\$basearch",
			enabled => 1,
		 	gpgcheck => 1,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
			failovermethod => 'priority',
			priority => 98,
			require => File['RPM-GPG-KEY-OSG'] ;

		'osg-upcoming-source':
			descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Upcoming - \$basearch - Source",
	#		baseurl => "http://repo.grid.iu.edu/osg/upcoming/el$lsbmajdistrelease/osg-upcoming-release/source/SRPMS",
			baseurl => "http://t2.unl.edu/osg/osg/upcoming/el$lsbmajdistrelease/release/source/SRPMS",
			enabled => 0,
	 		gpgcheck => 1,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
			failovermethod => 'priority',
			priority => 98,
			require => File['RPM-GPG-KEY-OSG'] ;

		'osg-upcoming-debug':
			descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Upcoming - \$basearch - Debug",
	#		baseurl => "http://repo.grid.iu.edu/osg/3.1/el$lsbmajdistrelease/osg-upcoming-release/\$basearch/debug",
			baseurl => "http://t2.unl.edu/osg/osg/upcoming/el$lsbmajdistrelease/release/\$basearch/debug",
			enabled => 0,
	 		gpgcheck => 1,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
			failovermethod => 'priority',
			priority => 98,
			require => File['RPM-GPG-KEY-OSG'] ;

      'osg-testing':
         descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Testing - \$basearch",
 #        mirrorlist => "http://repo.grid.iu.edu/mirror/osg/3.1/el$lsbmajdistrelease/testing/\$basearch",
			baseurl => "http://t2.unl.edu/osg/osg/3.1/el$lsbmajdistrelease/testing/\$basearch",
         enabled => 0,
         gpgcheck => 1,
         gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
         failovermethod => 'priority',
         priority => 98,
         require => File['RPM-GPG-KEY-OSG'] ;

      'osg-testing-source':
         descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Testing - \$basearch - Source",
 #        mirrorlist => "http://repo.grid.iu.edu/mirror/osg/3.1/el$lsbmajdistrelease/testing/source/SRPMS",
			baseurl => "http://t2.unl.edu/osg/osg/3.1/el$lsbmajdistrelease/testing/source/SRPMS",
         enabled => 0,
         gpgcheck => 1,
         gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
         failovermethod => 'priority',
         priority => 98,
         require => File['RPM-GPG-KEY-OSG'] ;

      'osg-testing-debug':
         descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Testing - \$basearch - Debug",
 #        mirrorlist => "http://repo.grid.iu.edu/mirror/osg/3.1/el$lsbmajdistrelease/testing/\$basearch/debug",
			baseurl => "http://t2.unl.edu/osg/osg/3.1/el$lsbmajdistrelease/testing/\$basearch/debug",
         enabled => 0,
         gpgcheck => 1,
         gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
         failovermethod => 'priority',
         priority => 98,
         require => File['RPM-GPG-KEY-OSG'] ;

       'osg-upcoming-testing':
         descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Upcoming Testing - \$basearch",
        mirrorlist => "http://repo.grid.iu.edu/mirror/osg/3.1/el$lsbmajdistrelease/osg-upcoming-testing/\$basearch",
			baseurl => "http://t2.unl.edu/osg/upcoming/el$lsbmajdistrelease/testing/\$basearch",
          enabled => 0,
         gpgcheck => 1,
         gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
         failovermethod => 'priority',
         priority => 98,
         require => File['RPM-GPG-KEY-OSG'] ;

      'osg-upcoming-testing-source':
         descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Upcoming Testing - \$basearch - Source",
        mirrorlist => "http://repo.grid.iu.edu/mirror/osg/3.1/el$lsbmajdistrelease/osg-upcoming-testing/source/SRPMS",
			baseurl => "http://t2.unl.edu/osg/upcoming/el$lsbmajdistrelease/testing/source/SRPMS",
         enabled => 0,
         gpgcheck => 1,
         gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
         failovermethod => 'priority',
         priority => 98,
         require => File['RPM-GPG-KEY-OSG'] ;

#      'osg-upcoming-testing-debug':
#         descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Upcoming Testing - \$basearch - Debug",
# #        mirrorlist => "http://repo.grid.iu.edu/mirror/osg/3.1/el$lsbmajdistrelease/osg-upcoming-testing/\$basearch/debug",
#			baseurl => "http://t2.unl.edu/osg/osg/3.1/el$lsbmajdistrelease/osg-upcoming-testing/\$basearch/debug",
#         enabled => 0,
#         gpgcheck => 1,
#         gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
#         failovermethod => 'priority',
#         priority => 98,
#         require => File['RPM-GPG-KEY-OSG'] ;

      'osg-development':
         descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Development - \$basearch",
  #       mirrorlist => "http://repo.grid.iu.edu/mirror/osg/3.1/el$lsbmajdistrelease/development/\$basearch",
			baseurl => "http://t2.unl.edu/osg/3.1/el$lsbmajdistrelease/development/\$basearch",
         enabled => 0,
         gpgcheck => 1,
         gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
         failovermethod => 'priority',
         priority => 98,
         require => File['RPM-GPG-KEY-OSG'] ;

      'osg-development-source':
         descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Development - \$basearch - Source",
  #       mirrorlist => "http://repo.grid.iu.edu/mirror/osg/3.1/el$lsbmajdistrelease/osg-development/source/SRPMS",
			baseurl => "http://t2.unl.edu/osg/3.1/el$lsbmajdistrelease/development/source/SRPMS",
         enabled => 0,
         gpgcheck => 1,
         gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
         failovermethod => 'priority',
         priority => 98,
         require => File['RPM-GPG-KEY-OSG'] ;

      'osg-development-debug':
         descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Development - \$basearch - Debug",
  #       mirrorlist => "http://repo.grid.iu.edu/mirror/osg/3.1/el$lsbmajdistrelease/development/\basearch/debug",
			baseurl => "http://t2.unl.edu/osg/osg/3.1/el$lsbmajdistrelease/development/\$basearch/debug",
         enabled => 0,
         gpgcheck => 1,
         gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
         failovermethod => 'priority',
         priority => 98,
         require => File['RPM-GPG-KEY-OSG'] ;

#      'osg-upcoming-development':
#         descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Upcoming Development - \$basearch",
#  #       mirrorlist => "http://repo.grid.iu.edu/mirror/osg/3.1/el$lsbmajdistrelease/osg-upcoming-development/\$basearch",
#			baseurl => "http://t2.unl.edu/osg/osg/3.1/el$lsbmajdistrelease/osg-upcoming-development/\$basearch",
#         enabled => 0,
#         gpgcheck => 1,
#         gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
#         failovermethod => 'priority',
#         priority => 98,
#         require => File['RPM-GPG-KEY-OSG'] ;

#      'osg-upcoming-development-source':
#         descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Upcoming Development - \$basearch - Source",
#  #       mirrorlist => "http://repo.grid.iu.edu/mirror/osg/3.1/el$lsbmajdistrelease/osg-upcoming-development/source/SRPMS",
#			baseurl => "http://t2.unl.edu/osg/osg/3.1/el$lsbmajdistrelease/osg-upcoming-development/source/SRPMS",
#         enabled => 0,
#         gpgcheck => 1,
#         gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
#         failovermethod => 'priority',
#         priority => 98,
#         require => File['RPM-GPG-KEY-OSG'] ;

#      'osg-upcoming-development-debug':
#         descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Upcoming Development - \$basearch - Debug",
#  #       mirrorlist => "http://repo.grid.iu.edu/mirror/osg/3.1/el$lsbmajdistrelease/osg-upcoming-development/\basearch/debug",
#			baseurl => "http://t2.unl.edu/osg/osg/3.1/el$lsbmajdistrelease/osg-upcoming-development/\$basearch/debug",
#         enabled => 0,
#         gpgcheck => 1,
#         gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
#         failovermethod => 'priority',
#         priority => 98,
#         require => File['RPM-GPG-KEY-OSG'] ;

      'osg-contrib':
         descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Contributed - \$basearch",
  #       mirrorlist => "http://repo.grid.iu.edu/mirror/osg/3.1/el$lsbmajdistrelease/osg-contrib/\$basearch",
			baseurl => "http://t2.unl.edu/osg/3.1/el$lsbmajdistrelease/contrib/\$basearch",
         enabled => 1,
         gpgcheck => 1,
         gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
         failovermethod => 'priority',
         priority => 98,
         require => File['RPM-GPG-KEY-OSG'] ;

      'osg-contrib-source':
         descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Contributed - \$basearch - Source",
  #       mirrorlist => "http://repo.grid.iu.edu/mirror/osg/3.1/el$lsbmajdistrelease/osg-contrib/source/SRPMS",
			baseurl => "http://t2.unl.edu/osg/osg/3.1/el$lsbmajdistrelease/contrib/source/SRPMS",
         enabled => 0,
         gpgcheck => 1,
         gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
         failovermethod => 'priority',
         priority => 98,
         require => File['RPM-GPG-KEY-OSG'] ;

      'osg-contrib-debug':
         descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Contributed - \$basearch - Debug",
  #       mirrorlist => "http://repo.grid.iu.edu/mirror/osg/3.1/el$lsbmajdistrelease/osg-contrib/\$basearch/debug",
			baseurl => "http://t2.unl.edu/osg/osg/3.1/el$lsbmajdistrelease/contrib/\$basearch/debug",
         enabled => 0,
         gpgcheck => 1,
         gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
         failovermethod => 'priority',
         priority => 98,
         require => File['RPM-GPG-KEY-OSG'] ;

#		'osg-minefield':
#			descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Build Repository - \$basearch",
#			baseurl => "http://koji-hub.batlab.org/mnt/koji/repos/el$lsbmajdihtstrelease-osg-development/latest/\$basearch/",
#			enabled => 0,
#	 		gpgcheck => 1,
#			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
#			failovermethod => 'priority',
#			priority => 98,
#			require => File['RPM-GPG-KEY-OSG'] ;

#		'osg-upcoming-minefield':
#			descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Upcoming Build Repository - \$basearch",
#			baseurl => "http://koji-hub.batlab.org/mnt/koji/repos/el$lsbmajdihtstrelease-osg-upcoming-development/latest/\$basearch/",
#			enabled => 0,
#	 		gpgcheck => 1,
#			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
#			failovermethod => 'priority',
#			priority => 98,
#			require => File['RPM-GPG-KEY-OSG'] ;

#		'osg-prerelease':
#			descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Prerelease Repository for Internal Use - \$basearch",
#			baseurl => "http://koji-hub.batlab.org/mnt/koji/repos/el$lsbmajdihtstrelease-osg-prerelease/latest/\$basearch/",
#			enabled => 0,
#	 		gpgcheck => 1,
#			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
#			failovermethod => 'priority',
#			priority => 98,
#			require => File['RPM-GPG-KEY-OSG'] ;

#		'osg-upcoming-prerelease':
#			descr => "OSG Software for Enterprise Linux $lsbmajdistrelease - Upcoming Prerelease Repository for Internal Use - \$basearch",
#			baseurl => "http://koji-hub.batlab.org/mnt/koji/repos/el$lsbmajdihtstrelease-osg-upcoming-prerelease/latest/\$basearch/",
#			enabled => 0,
#	 		gpgcheck => 1,
#			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-OSG',
#			failovermethod => 'priority',
#			priority => 98,
#			require => File['RPM-GPG-KEY-OSG'] ;



	}	# end yum::managed_yumrepo

}
