class projects::puppet_dockutil (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'puppet_dockutil':
		dir		=>	"${my_sourcedir}/Mine/puppet-dockutil",
		source	=>	'grahamgilbert/puppet-dockutil',
	}
}