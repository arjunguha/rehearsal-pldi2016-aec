class projects::recovery_hd_mountain_lion (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'recovery_hd_mountain_lion':
		dir		=>	"${my_sourcedir}/Mine/recovery-hd-mountain-lion",
		source	=>	'grahamgilbert/recovery-hd-mountain-lion',
	}
}