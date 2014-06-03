group { 'puppet': ensure => 'present' }
Exec { path => ['/usr/local/bin', '/opt/local/bin', '/usr/bin', '/usr/sbin', '/bin', '/sbin'] }

class system {
	exec { 'apt-get update':
	    command => '/usr/bin/apt-get update'
	}

	$corepackages = ["nfs-common", "memcached", "sendmail", "git"]
	package { $corepackages :
    ensure => latest,
    require => Exec["apt-get update"]
  }
}

include system
include apache2
include mysql55
include php54
include composer