class projects::training_site (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){

	boxen::project { 'training_site':
		dir		=>	"${my_sourcedir}/Work/training_site",
		source	=>	'pebbleit/training_site',
	}
}