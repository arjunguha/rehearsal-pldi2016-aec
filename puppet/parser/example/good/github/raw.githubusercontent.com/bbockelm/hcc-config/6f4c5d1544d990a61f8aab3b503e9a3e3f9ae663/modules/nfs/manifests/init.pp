#
# Class: nfs
#
# include nfs::server for fileservers
#

class nfs {

	package { "nfs-utils": ensure => present, }

}
