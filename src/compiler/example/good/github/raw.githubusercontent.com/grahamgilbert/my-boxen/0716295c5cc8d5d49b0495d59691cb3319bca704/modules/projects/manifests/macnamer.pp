class projects::macnamer (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'macnamer':
		dir		=>	"${my_sourcedir}/Mine/macnamer",
		source	=>	'grahamgilbert/macnamer',
	}
}