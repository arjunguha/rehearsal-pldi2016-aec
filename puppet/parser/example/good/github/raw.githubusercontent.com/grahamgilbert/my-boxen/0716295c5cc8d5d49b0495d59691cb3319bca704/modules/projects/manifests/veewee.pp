class projects::veewee (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){

	boxen::project { 'veewee':
		dir		=>	"${my_sourcedir}/Others/veewee",
		source	=>	'jedi4ever/veewee',
	}
}