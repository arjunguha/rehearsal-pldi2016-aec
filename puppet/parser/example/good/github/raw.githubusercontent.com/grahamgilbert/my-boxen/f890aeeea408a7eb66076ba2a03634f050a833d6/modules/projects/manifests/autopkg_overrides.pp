class projects::autopkg_overrides (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'autopkg-overrides':
		dir		=>	"${my_sourcedir}/Mine/autopkg-overrides",
		source	=>	'grahamgilbert/autopkg-overrides',
	}

}