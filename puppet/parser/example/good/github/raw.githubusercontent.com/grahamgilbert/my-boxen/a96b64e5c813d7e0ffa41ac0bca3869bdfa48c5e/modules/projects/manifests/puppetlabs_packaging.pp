class projects::puppetlabs_packaging (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'puppetlabs_packagin':
		dir		=> "${my_sourcedir}/Others/puppetlabs-puppet/ext/packaging",
		source	=> 'puppetlabs/puppet',
        require => Boxen::Project["puppet"],
	}

}