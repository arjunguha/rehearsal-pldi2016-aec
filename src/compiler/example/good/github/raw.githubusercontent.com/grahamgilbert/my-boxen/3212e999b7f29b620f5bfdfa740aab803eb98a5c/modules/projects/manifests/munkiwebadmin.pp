class projects::munkiwebadmin (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'munkiwebadmin':
		dir		=>	"${my_sourcedir}/Others/munkiwebadmin",
		source	=>	'https://code.google.com/p/munki.munkiwebadmin/',
	}
}