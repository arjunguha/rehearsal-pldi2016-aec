#
# Class: timezone::params
#

class timezone::params {

	$timezone_path = $operatingsystem ? {
		/(?i-mx:debian|ubuntu)/ => '/etc/timezone',
		/(?i-mx:redhat|centos|scientific|fedora)/ => '/etc/sysconfig/clock',
		/(?i-mx:freebsd)/ => '/etc/timezone-puppet',
	}

	$timezone_cmd = $operatingsystem ? {
		/(?i-mx:debian|ubuntu)/ => 'dpkg-reconfigure -f noninteractive tzdata',
		/(?i-mx:redhat|centos|scientific|fedora)/ => 'tzdata-update',
		/(?i-mx:freebsd)/ => 'cp /usr/share/zoneinfo/${timezone} /etc/localtime && adjkerntz -a',
	}

}
