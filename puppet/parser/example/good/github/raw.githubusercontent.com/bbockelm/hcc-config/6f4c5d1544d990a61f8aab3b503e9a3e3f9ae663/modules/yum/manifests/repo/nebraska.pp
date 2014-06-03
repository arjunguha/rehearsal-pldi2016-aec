
class yum::repo::nebraska {

	yum::managed_yumrepo {

	'nebraska':
		descr => "Nebraska RPMs for EL$lsbmajdistrelease - \$basearch",
		baseurl => $lsbmajdistrelease ? {
			5 => "http://t2.unl.edu/store/repos/nebraska/5/nebraska/\$basearch",
			6 => "http://t2.unl.edu/store/repos/nebraska/6/nebraska-el6/\$basearch",
			default => "http://t2.unl.edu/store/repos/nebraska/\$lsbmajdistrelease/nebraska/\$basearch",
		},
		enabled => 1,
	 	gpgcheck => 0,
		priority => 9 ;

	'nebraska-testing':
		descr => "Nebraska RPMs for EL$lsbmajdistrelease - \$basearch - Testing",
		baseurl => $lsbmajdistrelease ? {
			5 => "http://t2.unl.edu/store/repos/nebraska/5/nebraska-testing/\$basearch",
			6 => "http://t2.unl.edu/store/repos/nebraska/6/nebraska-el6-testing/\$basearch",
			default => "http://t2.unl.edu/store/repos/nebraska/\$lsbmajdistrelease/nebraska-testing/\$basearch",
		},
		enabled => 0,
	 	gpgcheck => 0,
		priority => 9 ;

	}	# end yum::managed_repo

}
