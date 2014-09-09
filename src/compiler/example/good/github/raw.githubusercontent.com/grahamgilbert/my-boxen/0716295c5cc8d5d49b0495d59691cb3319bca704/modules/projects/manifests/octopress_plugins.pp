class projects::octopress_plugins (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'octopress_plugins':
		dir		=>	"${my_sourcedir}/Others/octopress-plugins",
		source	=>	'bmc/octopress-plugins',
	}
}