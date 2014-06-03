class projects::pebble_munki_repo (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'munki-repo':
		dir		=>	"${my_sourcedir}/Work/munki-repo",
		source	=>	'pebbleit/munki-repo',
	}
}