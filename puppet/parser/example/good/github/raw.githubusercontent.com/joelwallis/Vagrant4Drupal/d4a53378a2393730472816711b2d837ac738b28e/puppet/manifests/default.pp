# vagrant4drupal provisioner
Exec {
	path => [
		'/usr/bin',
		'/bin', '/usr/sbin',
		'/sbin',
		'/usr/local/bin',
		'/usr/local/sbin'
	],
}
exec {
	'apt-get update':
		command => 'apt-get update && apt-get upgrade -y',
		timeout => 0,
}

include bootstrap
include apache
include php
include mysql
include phpmyadmin
include drush
