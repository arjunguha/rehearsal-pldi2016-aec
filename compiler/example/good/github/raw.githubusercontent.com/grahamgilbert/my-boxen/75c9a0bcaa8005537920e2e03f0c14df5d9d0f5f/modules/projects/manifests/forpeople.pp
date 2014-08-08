class projects::forpeople (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'forpeople':
		dir		=>	"${my_sourcedir}/Work/forpeople",
		source	=>	'pebbleit/forpeople',
	}
}