class projects::rumps (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	
	
	boxen::project { 'rumps':
		dir		=>	"${my_sourcedir}/Others/rumps",
		source	=>	'jaredks/rumps',
	}
}