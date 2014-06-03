class people::grahamgilbert::loginitems (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	osx_login_item { 'Alfred 2':
		name => 'Alfred 2',
		path => '/Applications/Alfred 2.app',
		hidden => true,
		require => Class['alfred'],
	}
		
		
	osx_login_item { 'Bartender':
		name => 'Bartender',
		path => '/Applications/Bartender.app',
		hidden => true,
		require => Package['Bartender'],
	}	
		
	osx_login_item { 'Dropbox':
	   name => 'Dropbox',
	   path => '/Applications/Dropbox.app',
	   hidden => true,
	   require => Class['dropbox'],
	}
}