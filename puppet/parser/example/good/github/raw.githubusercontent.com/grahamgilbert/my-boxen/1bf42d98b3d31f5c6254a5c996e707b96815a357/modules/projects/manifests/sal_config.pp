class projects::sal_config (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	boxen::project { 'sal_config':
		dir		=>	"${my_sourcedir}/Mine/sal/config",
		source	=>	'pebbleit/sal-config',
        require =>  Boxen::Project['sal'],
	}
}