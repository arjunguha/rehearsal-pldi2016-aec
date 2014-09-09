class projects::munki (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'munki':
		dir		=>	"${my_sourcedir}/Others/munki",
		source	=>	'https://code.google.com/p/munki/',
	}
}