class projects::saved (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'saved':
		dir		=>	"${my_sourcedir}/Mine/saved",
		source	=>	'grahamgilbert/saved',
	}
}