class projects::sal_plugins (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'sal_plugins':
		dir		=>	"${my_sourcedir}/Mine/sal-plugins",
		source	=>	'grahamgilbert/sal-plugins',
	}
}