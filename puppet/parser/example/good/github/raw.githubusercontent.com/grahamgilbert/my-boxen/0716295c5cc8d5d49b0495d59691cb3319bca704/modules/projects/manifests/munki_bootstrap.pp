class projects::munki_bootstrap (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'munki_bootstrap':
		dir		=>	"${my_sourcedir}/Mine/munki-bootstrap",
		source	=>	'grahamgilbert/Munki-Bootstrap',
	}
}