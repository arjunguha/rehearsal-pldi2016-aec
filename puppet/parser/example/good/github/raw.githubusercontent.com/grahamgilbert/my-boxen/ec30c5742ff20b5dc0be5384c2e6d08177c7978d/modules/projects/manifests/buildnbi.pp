class projects::buildnbi (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	
	
	boxen::project { 'buildnbi':
		dir		=>	"${my_sourcedir}/Others/buildnbi",
		source	=>	'https://bitbucket.org/bruienne/buildnbi.git',
	}
    
}