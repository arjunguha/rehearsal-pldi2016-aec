class projects::the_luggage (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){

	boxen::project { 'the_luggage':
		dir		=>	"${my_sourcedir}/Others/luggage",
		source	=>	'unixorn/luggage',
	}
}