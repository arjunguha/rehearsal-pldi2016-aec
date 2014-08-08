
class yum::repo::sl6 {

	yum::managed_yumrepo {

		# the following are the repos from a stock SL6 install
		'sl':
			descr => "Scientific Linux \$releasever - \$basearch",
			baseurl => "http://hcc-mirror.unl.edu/scientific-linux/\$releasever/\$basearch/os/ http://ftp.scientificlinux.org/linux/scientific/\$releasever/\$basearch/os/",
			enabled => 1,
			gpgcheck => 1,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl',
			priority => 10 ;

		'sl-security':
			descr => "Scientific Linux \$releasever - \$basearch - security updates",
			baseurl => "http://hcc-mirror.unl.edu/scientific-linux/\$releasever/\$basearch/updates/security/ http://ftp.scientificlinux.org/linux/scientific/\$releasever/\$basearch/updates/security/",
			enabled => 1,
			gpgcheck => 1,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl',
			priority => 10 ;

		'sl-source':
			descr => "Scientific Linux \$releasever - \$basearch - Source",
			baseurl => "http://hcc-mirror.unl.edu/scientific-linux/\$releasever/SRPMS/ http://ftp.scientificlinux.org/linux/scientific/\$releasever/SRPMS/",
			enabled => 0,
			gpgcheck => 1,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl',
			priority => 10 ;


		# the following are from the stock SL6 sl-other.repo
		'sl-fastbugs':
			descr => "Scientific Linux \$releasever - \$basearch - fastbug updates",
			baseurl => "http://hcc-mirror.unl.edu/scientific-linux/\$releasever/\$basearch/updates/fastbugs/ http://ftp.scientificlinux.org/linux/scientific/\$releasever/\$basearch/updates/fastbugs/",
			enabled => 0,
			gpgcheck => 1,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl',
			priority => 10 ;

		'sl-debuginfo':
			descr => "Scientific Linux Debuginfo",
			baseurl => "http://hcc-mirror.unl.edu/scientific-linux/\$releasever/archive/debuginfo/ http://ftp.scientificlinux.org/linux/scientific/\$releasever/archive/debuginfo/",
			enabled => 0,
			gpgcheck => 1,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl',
			priority => 10 ;

		'sl-testing':
			descr => "Scientific Linux Testing - \$basearch",
			baseurl => "http://hcc-mirror.unl.edu/scientific-linux/6rolling/testing/\$basearch/ http://ftp.scientificlinux.org/linux/scientific/6rolling/testing/\$basearch/",
			enabled => 0,
			gpgcheck => 0,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl',
			priority => 10 ;

		'sl-testing-source':
			descr => "Scientific Linux Testing - Source",
			baseurl => "http://hcc-mirror.unl.edu/scientific-linux/6rolling/testing/SRPMS/ http://ftp.scientificlinux.org/linux/scientific/6rolling/testing/SRPMS/",
			enabled => 0,
			gpgcheck => 0,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl',
			priority => 10 ;

	}	# end yum::managed_yumrepo

}
