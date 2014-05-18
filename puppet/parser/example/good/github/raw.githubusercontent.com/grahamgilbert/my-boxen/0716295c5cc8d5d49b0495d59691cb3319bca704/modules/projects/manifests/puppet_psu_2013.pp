class projects::puppet_psu_2013 (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'puppet_psu_2013':
		dir		=>	"${my_sourcedir}/Mine/puppet_psu_2013",
		source	=>	'grahamgilbert/puppet_psu_2013',
	}
}