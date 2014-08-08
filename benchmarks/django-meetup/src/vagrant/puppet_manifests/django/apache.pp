# configure apache
file { '/var/www/django.wsgi':
	require => [Package['apache2'],Package['libapache2-mod-wsgi']],
	source => '/tmp/vagrant-puppet/manifests/files/django.wsgi',
	owner => 'root',
	group => 'root',
	mode => '644',
	}

file { '/etc/apache2/sites-available/django.local.conf':
	require => [ Package['apache2'], Package['libapache2-mod-wsgi'], File['/var/www/django.wsgi']],
	source => '/tmp/vagrant-puppet/manifests/files/django.local.conf',
	owner => 'root',
	group => 'root',
	mode => '644',
	}
	
file { '/etc/apache2/sites-enabled/django.local.conf':
	ensure => 'link',
	target => '/etc/apache2/sites-available/django.local.conf',
	require => File['/etc/apache2/sites-available/django.local.conf'],
	owner => 'root',
	group => 'root',
	mode => '644',
	}
	
# setup phpmyadmin site
file { '/usr/local/bin/phpmyadmininstall.sh':
	source => '/tmp/vagrant-puppet/manifests/files/phpmyadmininstall.sh',
	require => [Package['apache2'], Package['mysql-server'], Package['php5-mysql'], Package['php5-mcrypt'], File['/var/www/phpmyadmin/']],
	owner => 'root',
	group => 'root',
	mode => '744',
	}
file { '/var/www/phpmyadmin/':
	ensure => 'directory',
	require => Package['apache2'],
	owner => 'www-data',
	group => 'www-data',
	mode => '755',
	}
exec { 'install phpmyadmin':
	require => [File['/var/www/phpmyadmin/'], Exec['set mysql root password']],
	command => "/usr/local/bin/phpmyadmininstall.sh",
	subscribe => File['/usr/local/bin/phpmyadmininstall.sh'],
	refreshonly => true,
	}
file { '/var/www/phpmyadmin/config.inc.php':
	source => '/tmp/vagrant-puppet/manifests/files/phpmyadmin/config.inc.php',
	require => Exec['install phpmyadmin'],
	owner => 'root',
	group => 'root',
	mode => '644',
	}
	

# setup phpmyadmin apache config
file { '/etc/apache2/sites-available/phpmyadmin.django.local.conf':
	require => [Package['apache2'], Package['mysql-server'], Package['php5-mysql'], Package['php5-mcrypt'], File['/var/www/phpmyadmin/config.inc.php']],
	source => '/tmp/vagrant-puppet/manifests/files/phpmyadmin.django.local.conf',
	owner => 'root',
	group => 'root',
	mode => '644',
	}
file { '/etc/apache2/sites-enabled/phpmyadmin.django.local.conf':
	ensure => 'link',
	target => '/etc/apache2/sites-available/phpmyadmin.django.local.conf',
	require => File['/etc/apache2/sites-available/phpmyadmin.django.local.conf'],
	owner => 'root',
	group => 'root',
	mode => '644',
	}
exec { '/etc/init.d/apache2 restart;exit 0':
	subscribe => [File['/etc/apache2/sites-available/phpmyadmin.django.local.conf'], File['/etc/apache2/sites-enabled/phpmyadmin.django.local.conf'], File['/etc/apache2/sites-enabled/django.local.conf'], File['/etc/apache2/sites-available/django.local.conf'], File['/var/www/django.wsgi']],
	refreshonly => true,
	}
