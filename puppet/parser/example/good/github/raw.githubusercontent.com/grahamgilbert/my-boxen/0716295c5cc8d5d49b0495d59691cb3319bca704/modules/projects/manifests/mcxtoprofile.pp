class projects::mcxtoprofile (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'mcxtoprofile':
		dir		=>	"${my_sourcedir}/Others/mcxtoprofile",
		source	=>	'timsutton/mcxToProfile',
	}
}