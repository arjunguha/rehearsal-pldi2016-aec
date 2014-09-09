
class yum::repo::epel {

	# NOTE: EPEL GPG key location is different between el5 and el6
	#       set once here, used below in each repo
	$epel_gpgkey_filename = $lsbmajdistrelease ? {
		6 => 'RPM-GPG-KEY-EPEL-6',
		5 => 'RPM-GPG-KEY-EPEL',
		default => 'RPM-GPG-KEY-EPEL-6',
	}

	# EPEL-6 gpg key
	# version = 0608b895
	# release = 4bd22942

	file { "RPM-GPG-KEY-EPEL":
		path => "/etc/pki/rpm-gpg/$epel_gpgkey_filename",
		source => "puppet:///modules/yum/rpm-gpg/$epel_gpgkey_filename",
		ensure => present,
		owner => 'root', group => 'root', mode => '0644',
	}

	yum::managed_yumrepo {

		'epel':
			descr => "Extra Packages for Enterprise Linux $lsbmajdistrelease - \$basearch",
#			mirrorlist => "http://mirrors.fedoraproject.org/mirrorlist?repo=epel-$lsbmajdistrelease&arch=\$basearch",
			baseurl => "http://hcc-mirror.unl.edu/fedora/epel/$lsbmajdistrelease/\$basearch",
			enabled => 1,
	 		gpgcheck => 1,
			gpgkey => "file:///etc/pki/rpm-gpg/$epel_gpgkey_filename",
			failovermethod => 'priority',
			priority => 99,
			require => File['RPM-GPG-KEY-EPEL'] ;

		'epel-debuginfo':
			descr => "Extra Packages for Enterprise Linux $lsbmajdistrelease - \$basearch - Debug",
			mirrorlist => "http://mirrors.fedoraproject.org/mirrorlist?repo=epel-debug-$lsbmajdistrelease&arch=\$basearch",
			enabled => 0,
			gpgcheck => 1,
			gpgkey => "file:///etc/pki/rpm-gpg/$epel_gpgkey_filename",
			failovermethod => 'priority',
			priority => 99,
			require => File['RPM-GPG-KEY-EPEL'] ;

		'epel-source':
			descr => "Extra Packages for Enterprise Linux $lsbmajdistrelease - \$basearch - Source",
			mirrorlist => "http://mirrors.fedoraproject.org/mirrorlist?repo=epel-source-$lsbmajdistrelease&arch=\$basearch",
			enabled => 0,
			gpgcheck => 1,
			gpgkey => "file:///etc/pki/rpm-gpg/$epel_gpgkey_filename",
			failovermethod => 'priority',
			priority => 99,
			require => File['RPM-GPG-KEY-EPEL'] ;

		'epel-testing':
			descr => "Extra Packages for Enterprise Linux $lsbmajdistrelease - Testing - \$basearch",
			mirrorlist => "http://mirrors.fedoraproject.org/mirrorlist?repo=testing-epel$lsbmajdistrelease&arch=\$basearch",
			enabled => 0,
			gpgcheck => 1,
			gpgkey => "file:///etc/pki/rpm-gpg/$epel_gpgkey_filename",
			failovermethod => 'priority',
			priority => 99,
			require => File['RPM-GPG-KEY-EPEL'] ;

		'epel-testing-debuginfo':
			descr => "Extra Packages for Enterprise Linux $lsbmajdistrelease - Testing - \$basearch - Debug",
			mirrorlist => "http://mirrors.fedoraproject.org/mirrorlist?repo=testing-debug-epel$lsbmajdistrelease&arch=\$basearch",
			enabled => 0,
			gpgcheck => 1,
			gpgkey => "file:///etc/pki/rpm-gpg/$epel_gpgkey_filename",
			failovermethod => 'priority',
			priority => 99,
			require => File['RPM-GPG-KEY-EPEL'] ;

		'epel-testing-source':
			descr => "Extra Packages for Enterprise Linux $lsbmajdistrelease - Testing - \$basearch - Source",
			mirrorlist => "http://mirrors.fedoraproject.org/mirrorlist?repo=testing-source-epel$lsbmajdistrelease&arch=\$basearch",
			enabled => 0,
			gpgcheck => 1,
			gpgkey => "file:///etc/pki/rpm-gpg/$epel_gpgkey_filename",
			failovermethod => 'priority',
			priority => 99,
			require => File['RPM-GPG-KEY-EPEL'] ;

	}	# end yum::managed_yumrepo

}
