class projects::pebble_puppet (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'pebble_puppet':
		dir		=>	"${my_sourcedir}/Work/puppet",
		source	=>	'pebbleit/puppet',
	}
    
	boxen::project { 'pebble_customer':
		dir		=>	"${my_sourcedir}/Work/customer",
		source	=>	'pebbleit/customer',
	}
    
	boxen::project { 'pebble_hieradata':
		dir		=>	"${my_sourcedir}/Work/hieradata",
		source	=>	'pebbleit/hieradata',
	}
}