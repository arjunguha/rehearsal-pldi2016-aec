class osg-ce::install {

	# used to be from params ... can't use - in class names now, FIXME FIXME FIXME
	package { 'osg-ce-condor':
		ensure => present,
	}

   package { "osg-info-services":
      ensure => present,
   }

}
