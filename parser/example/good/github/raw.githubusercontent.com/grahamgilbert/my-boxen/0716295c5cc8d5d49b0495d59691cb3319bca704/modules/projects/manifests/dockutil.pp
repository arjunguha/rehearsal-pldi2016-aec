class projects::dockutil (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){

	boxen::project { 'dockutil':
		dir		=>	"${my_sourcedir}/Others/dockutil",
		source	=>	'kcrawford/dockutil',
	}
}