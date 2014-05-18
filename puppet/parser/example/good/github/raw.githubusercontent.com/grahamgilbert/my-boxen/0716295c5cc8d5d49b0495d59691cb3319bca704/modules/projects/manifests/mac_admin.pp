class projects::mac_admin (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	
	
	boxen::project { 'mac_admin':
		dir		=>	"${my_sourcedir}/Mine/puppet-mac_admin",
		source	=>	'grahamgilbert/puppet-mac_admin',
	}
}