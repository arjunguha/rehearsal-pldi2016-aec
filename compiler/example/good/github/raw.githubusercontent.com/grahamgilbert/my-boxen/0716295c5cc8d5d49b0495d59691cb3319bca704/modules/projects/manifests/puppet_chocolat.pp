class projects::puppet_chocolat (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'puppet_chocolat':
		dir		=>	"${my_sourcedir}/Mine/puppet-chocolat",
		source	=>	'grahamgilbert/puppet-chocolat',
	}
}