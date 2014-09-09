class projects::blog (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	boxen::project { 'blog':
		dir		=>	"${my_sourcedir}/Mine/blog",
		source	=>	'grahamgilbert/blog',
	}
}