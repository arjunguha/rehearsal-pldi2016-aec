class projects::rcoleman_mac_profiles_handler (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'rocleman_mac_profiles_handler':
		dir		=>	"${my_sourcedir}/Mine/rcoleman-mac_profiles_handler",
		source	=>	'grahamgilbert/rcoleman-mac_profiles_handler',
	}
}