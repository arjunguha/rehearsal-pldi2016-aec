class projects::installlionpkg (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	
	
	boxen::project { 'installlionpkg':
		dir		=>	"${my_sourcedir}/Others/installlionpkg",
		source	=>	'https://code.google.com/p/munki.installlionpkg/',
	}
}