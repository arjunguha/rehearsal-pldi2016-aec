class projects::puppet_crypt (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	#include python
	
	boxen::project { 'puppet-crypt':
		dir		=>	"${my_sourcedir}/Mine/puppet-crypt",
		source	=>	'grahamgilbert/puppet-crypt',
	}

}