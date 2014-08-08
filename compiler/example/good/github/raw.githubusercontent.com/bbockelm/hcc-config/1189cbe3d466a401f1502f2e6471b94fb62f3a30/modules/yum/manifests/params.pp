class yum::params {

	# how to manage yum auto update
	$update = $yum_update ? {
		"cron"     => "cron",
		"updatesd" => "updatesd",
		default    => "off",
	}

	# default to epel, hcc, and osg
	# override in node def if we don't want one
	$extrarepo = $yum_extrarepo ? {
		""      => [ 'epel', 'hcc', 'osg' ],
		default => $yum_extrarepo,
	}

	# name of yum priority package
	$packagename_yumpriority = $lsbmajdistrelease ? {
		5 => "yum-priorities",
		6 => "yum-plugin-priorities",
		default => "yum-plugin-priorities",
	}

}
