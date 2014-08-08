class drush {
	exec {
		'pear channel-discover':
			command => 'pear channel-discover pear.drush.org',
			require => Package['php-pear'],
			onlyif => 'test ! -f /usr/bin/drush',
	}
	exec {
		'pear install':
			command => 'pear install drush/drush',
			require => Exec['pear channel-discover'],
			onlyif => 'test ! -f /usr/bin/drush',
	}
	exec {
		'drush':
			require => Exec['pear install'],
			onlyif => 'test ! -f /usr/bin/drush',
	}
	# @todo: install kraftwagen
}
