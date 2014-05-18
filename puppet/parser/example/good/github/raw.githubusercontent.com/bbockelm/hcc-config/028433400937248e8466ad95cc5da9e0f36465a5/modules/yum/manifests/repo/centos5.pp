
class yum::repo::centos5 {

	yum::managed_yumrepo {

		# the following are from a stock CentOS 5.7 install
		'base':
			descr => "CentOS-\$releasever - Base",
			baseurl => "http://hcc-mirror.unl.edu/centos/\$releasever/os/\$basearch/ http://mirror.centos.org/centos/\$releasever/os/\$basearch/",
			enabled => 1,
			gpgcheck => 1,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-CentOS-5',
			priority => 10 ;

		'updates':
			descr => "CentOS-\$releasever - Updates",
			baseurl => "http://hcc-mirror.unl.edu/centos/\$releasever/updates/\$basearch/ http://mirror.centos.org/centos/\$releasever/updates/\$basearch/",
			enabled => 1,
			gpgcheck => 1,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-CentOS-5',
			priority => 10 ;

		'extras':
			descr => "CentOS-\$releasever - Extras",
			baseurl => "http://hcc-mirror.unl.edu/centos/\$releasever/extras/\$basearch/ http://mirror.centos.org/centos/\$releasever/extras/\$basearch/",
			enabled => 1,
			gpgcheck => 1,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-CentOS-5',
			priority => 10 ;

		'centosplus':
			descr => "CentOS-\$releasever - Plus",
			baseurl => "http://hcc-mirror.unl.edu/centos/\$releasever/centosplus/\$basearch/ http://mirror.centos.org/centos/\$releasever/centosplus/\$basearch/",
			enabled => 0,
			gpgcheck => 1,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-CentOS-5',
			priority => 10 ;

		'contrib':
			descr => "CentOS-\$releasever - Contrib",
			baseurl => "http://hcc-mirror.unl.edu/centos/\$releasever/contrib/\$basearch/ http://mirror.centos.org/centos/\$releasever/contrib/\$basearch/",
			enabled => 0,
			gpgcheck => 1,
			gpgkey => 'file:///etc/pki/rpm-gpg/RPM-GPG-KEY-CentOS-5',
			priority => 10 ;

	}	# end yum::managed_yumrepo

}
