
class yum::repo::sl5 {

	yum::managed_yumrepo {

		# the following are the repos from a stock SL5 install

		'sl-base':
			descr => 'SL 5 base',
			baseurl => 'http://hcc-mirror.unl.edu/scientific-linux/5x/$basearch/SL http://ftp.scientificlinux.org/linux/scientific/5x/$basearch/SL',
			enabled => 1,
			gpgcheck => 0,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl5 file:///etc/pki/rpm-gpg/RPM-GPG-KEY-csieh file:///etc/pki/rpm-gpg/RPM-GPG-KEY-dawson file:///etc/pki/rpm-gpg/RPM-GPG-KEY-jpolok file:///etc/pki/rpm-gpg/RPM-GPG-KEY-cern file:///etc/pki/rpm-gpg/RPM-GPG-KEY-CentOS-5',
			priority => 10 ;

		'sl-fastbugs':
			descr => 'SL 5 fastbugs area',
			baseurl => 'http://hcc-mirror.unl.edu/scientific-linux/5x/$basearch/updates/fastbugs http://ftp.scientificlinux.org/linux/scientific/5x/$basearch/updates/fastbugs',
			enabled => 0,
			gpgcheck => 0,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl5 file:///etc/pki/rpm-gpg/RPM-GPG-KEY-csieh file:///etc/pki/rpm-gpg/RPM-GPG-KEY-dawson file:///etc/pki/rpm-gpg/RPM-GPG-KEY-jpolok file:///etc/pki/rpm-gpg/RPM-GPG-KEY-cern file:///etc/pki/rpm-gpg/RPM-GPG-KEY-CentOS-5',
			priority => 10 ;

		'sl-security':
			descr => 'SL 5 security updates',
			baseurl => 'http://hcc-mirror.unl.edu/scientific-linux/5x/$basearch/updates/security http://ftp.scientificlinux.org/linux/scientific/5x/$basearch/updates/security',
			enabled => 1,
			gpgcheck => 0,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl5 file:///etc/pki/rpm-gpg/RPM-GPG-KEY-csieh file:///etc/pki/rpm-gpg/RPM-GPG-KEY-dawson file:///etc/pki/rpm-gpg/RPM-GPG-KEY-jpolok file:///etc/pki/rpm-gpg/RPM-GPG-KEY-cern file:///etc/pki/rpm-gpg/RPM-GPG-KEY-CentOS-5',
			priority => 10 ;

		'sl-contrib':
			descr => 'Scientific Linux 5 contrib area',
			baseurl => 'http://hcc-mirror.unl.edu/scientific-linux/5x/$basearch/contrib http://ftp.scientificlinux.org/linux/scientific/5x/$basearch/contrib',
			enabled => 0,
			gpgcheck => 0,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl5 file:///etc/pki/rpm-gpg/RPM-GPG-KEY-csieh file:///etc/pki/rpm-gpg/RPM-GPG-KEY-dawson file:///etc/pki/rpm-gpg/RPM-GPG-KEY-jpolok file:///etc/pki/rpm-gpg/RPM-GPG-KEY-cern file:///etc/pki/rpm-gpg/RPM-GPG-KEY-CentOS-5',
			priority => 10 ;

		'sl-debuginfo':
			descr => 'Scientific Linux 5 debuginfo rpm\'s',
			baseurl => 'http://hcc-mirror.unl.edu/scientific-linux/5x/archive/debuginfo http://ftp.scientificlinux.org/linux/scientific/5x/archive/debuginfo',
			enabled => 0,
			gpgcheck => 0,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl5 file:///etc/pki/rpm-gpg/RPM-GPG-KEY-csieh file:///etc/pki/rpm-gpg/RPM-GPG-KEY-dawson file:///etc/pki/rpm-gpg/RPM-GPG-KEY-jpolok file:///etc/pki/rpm-gpg/RPM-GPG-KEY-cern file:///etc/pki/rpm-gpg/RPM-GPG-KEY-CentOS-5',
			priority => 10 ;

		'sl-source':
			descr => 'Scientific Linux 5 source rpm\'s (src.rpm)',
			baseurl => 'http://hcc-mirror.unl.edu/scientific-linux/5x/SRPMS http://ftp.scientificlinux.org/linux/scientific/5x/SRPMS',
			enabled => 0,
			gpgcheck => 0,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl5 file:///etc/pki/rpm-gpg/RPM-GPG-KEY-csieh file:///etc/pki/rpm-gpg/RPM-GPG-KEY-dawson file:///etc/pki/rpm-gpg/RPM-GPG-KEY-jpolok file:///etc/pki/rpm-gpg/RPM-GPG-KEY-cern file:///etc/pki/rpm-gpg/RPM-GPG-KEY-CentOS-5',
			priority => 10 ;

		'sl-testing':
			descr => 'Scientific Linux 5 testing area',
			baseurl => 'http://hcc-mirror.unl.edu/scientific-linux/5rolling/testing/$basearch http://ftp.scientificlinux.org/linux/scientific/5rolling/testing/$basearch',
			enabled => 0,
			gpgcheck => 0,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl file:///etc/pki/rpm-gpg/RPM-GPG-KEY-sl5 file:///etc/pki/rpm-gpg/RPM-GPG-KEY-csieh file:///etc/pki/rpm-gpg/RPM-GPG-KEY-dawson file:///etc/pki/rpm-gpg/RPM-GPG-KEY-jpolok file:///etc/pki/rpm-gpg/RPM-GPG-KEY-cern file:///etc/pki/rpm-gpg/RPM-GPG-KEY-CentOS-5',
			priority => 10 ;

	}	# end yum::managed_yumrepo

}
