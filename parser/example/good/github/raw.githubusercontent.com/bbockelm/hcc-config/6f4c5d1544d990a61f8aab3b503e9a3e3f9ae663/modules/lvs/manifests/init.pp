class lvs {

	# NOTE: piranha package includes ipvsadm, and is 'official' source
	#       of the /etc/sysconfig/ha/lvs.cf file
	$lvs_package_list = [ "piranha" ]
	package { $lvs_package_list: ensure => present }

}
