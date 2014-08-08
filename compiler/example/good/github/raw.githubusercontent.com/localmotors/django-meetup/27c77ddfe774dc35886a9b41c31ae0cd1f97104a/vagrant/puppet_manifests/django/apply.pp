
# Install the needed programs (making sure the hosts file is setup first)
Package { ensure => "installed", require => Exec['apt-get update'], }
$programs = [ "apache2", "mysql-server", "python-pip", "git-core", "python-imaging", "python-mysqldb", ]
package { $programs:
	}
package { 'libapache2-mod-wsgi':
	require => Package['apache2'],
	}
package { 'php5':
	require => Package['apache2'],
	}
package { 'php5-mysql':
	require => [Package['mysql-server'],Package['apache2']],
	}
package { 'php5-mcrypt':
	require => [Package['apache2'], Package['php5']],
	}

exec { 'apt-get update':
	command => 'apt-get update',
	}
	
# Set default path for exec
Exec { path => "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
	}

# import other manifests
import "mysql.pp"
import "apache.pp"
import "djangostuff.pp"
