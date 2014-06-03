class projects::sal (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	boxen::project { 'sal':
		dir		=>	"${my_sourcedir}/Mine/sal",
		source	=>	'grahamgilbert/sal',
	}
}