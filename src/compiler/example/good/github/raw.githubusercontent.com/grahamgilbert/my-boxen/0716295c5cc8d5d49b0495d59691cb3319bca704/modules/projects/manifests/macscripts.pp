class projects::macscripts (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'macscripts':
		dir		=>	"${my_sourcedir}/Mine/macscripts",
		source	=>	'grahamgilbert/macscripts',
	}
}