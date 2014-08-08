class projects::brit_school (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'brit_school':
		dir		=>	"${my_sourcedir}/Work/brit-school",
		source	=>	'pebbleit/brit-school',
	}
}