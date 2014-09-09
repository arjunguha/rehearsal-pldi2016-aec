class projects::pebble_internal (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'pebble_internal':
		dir		=>	"${my_sourcedir}/Work/pebble-internal",
		source	=>	'pebbleit/Pebble-Internal',
	}
}