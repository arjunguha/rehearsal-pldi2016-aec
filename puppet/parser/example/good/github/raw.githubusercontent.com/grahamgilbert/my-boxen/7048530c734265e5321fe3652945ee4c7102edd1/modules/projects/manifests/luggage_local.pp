class projects::luggage_local (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){

	boxen::project { 'luggage_local':
		dir		=>	"${my_sourcedir}/Mine/luggage_local",
		source	=>	'grahamgilbert/luggage_local',
	}
}