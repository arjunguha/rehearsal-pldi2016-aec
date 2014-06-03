
class yum::repo::nginx {

	yum::managed_yumrepo {

	'nginx':
		descr => "nginx repo for RHEL$lsbmajdistrelease",
		baseurl => "http://nginx.org/packages/rhel/$lsbmajdistrelease/\$basearch/",
		enabled => 1,
	 	gpgcheck => 0,
		priority => 8 ;

	}

}
