class projects::rtrouton_scripts (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	
	
	boxen::project { 'rtrouton_scripts':
		dir		=>	"${my_sourcedir}/Others/rtrouton_scripts",
		source	=>	'rtrouton/rtrouton_scripts',
	}
}