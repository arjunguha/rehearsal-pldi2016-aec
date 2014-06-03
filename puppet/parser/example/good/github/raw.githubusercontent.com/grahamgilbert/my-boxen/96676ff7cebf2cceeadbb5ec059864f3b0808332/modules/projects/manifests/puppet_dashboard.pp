class projects::puppet_dashboard (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'puppetlabs-dashboard':
		dir		=>	"${my_sourcedir}/Mine/puppetlabs-dashboard",
		source	=>	'grahamgilbert/puppetlabs-dashboard',
	}
}