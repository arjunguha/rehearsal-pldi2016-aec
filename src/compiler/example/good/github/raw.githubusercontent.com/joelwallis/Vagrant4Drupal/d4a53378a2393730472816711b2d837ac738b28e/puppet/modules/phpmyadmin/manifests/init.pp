class phpmyadmin {
	package {
		'phpmyadmin':
			ensure  => present,
			require => Package['apache2', 'mysql-server', 'php5', 'php5-mcrypt', 'php5-mysql'],
	}
	file {
		'/etc/apache2/conf.d/phpmyadmin.conf':
			ensure => link,
			target => '/etc/phpmyadmin/apache.conf',
			require => Package['apache2'],
			notify => Service['apache2'],
	}
	exec {
		'vagrant4drupal--config.inc.php':
			command => 'git clone https://gist.github.com/5550784.git /opt/vagrant4drupal--config.inc.php',
			require => Package['git'],
			onlyif => 'test ! -d /opt/vagrant4drupal--config.inc.php/.git',
	}
	exec {
		'ln config.inc.php':
			command => 'ln -fs /etc/phpmyadmin/config.inc.php /opt/vagrant4drupal--config.inc.php/vagrant4drupal--config.inc.php',
			# onlyif => 'test ! -L /etc/phpmyadmin/config.inc.php',
	}
}
