class role_red-srm {

	$mountsHDFS = "True"

   include general

   include ganglia
	include hostcert
	include bestman
	include hadoop

#   include hadoop
#   include bestman
#   include osg-ca-certs
#   include hostcert

}
