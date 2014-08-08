class projects::vagrant (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'vagrant':
		dir		=>	"${my_sourcedir}/Others/vagrant",
		source	=>	'mitchellh/vagrant',
	}
}