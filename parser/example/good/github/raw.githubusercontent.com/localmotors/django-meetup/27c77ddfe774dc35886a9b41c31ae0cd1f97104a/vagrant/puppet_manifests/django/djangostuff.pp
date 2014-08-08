# install django
file { '/usr/local/bin/djangoclone.sh':
	source => '/tmp/vagrant-puppet/manifests/files/djangoclone.sh',
	owner => 'root',
	group => 'root',
	mode => '744',
	}

exec { "djangoclone":
	require => [Package["git-core"], Package["apache2"]],
	command => "/usr/local/bin/djangoclone.sh",
	subscribe => File['/usr/local/bin/djangoclone.sh'],
	refreshonly => true,
	timeout => 0,
	}
