class projects::loginlog (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'loginlog':
		dir		=>	"${my_sourcedir}/Others/loginlog",
		source	=>	'MagerValp/LoginLog',
	}
}