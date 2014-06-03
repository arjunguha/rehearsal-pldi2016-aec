class projects::puppet_bootstrap (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){

	boxen::project { 'puppet_bootstrap':
		dir		=>	"${my_sourcedir}/Work/puppet-bootstrap",
		source	=>	'pebbleit/puppet-bootstrap',
	}
}