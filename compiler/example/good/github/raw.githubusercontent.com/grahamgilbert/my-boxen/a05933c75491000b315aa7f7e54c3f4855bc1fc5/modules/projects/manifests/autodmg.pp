class projects::autodmg (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	
	
	boxen::project { 'autodmg':
		dir		=>	"${my_sourcedir}/Others/autodmg",
		source	=>	'MagerValp/AutoDMG',
	}
}