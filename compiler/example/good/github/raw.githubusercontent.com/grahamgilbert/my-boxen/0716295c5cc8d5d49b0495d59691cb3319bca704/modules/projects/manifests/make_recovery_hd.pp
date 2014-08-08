class projects::make_recovery_hd (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'make_recovery_hd':
		dir		=>	"${my_sourcedir}/Mine/make-recovery-hd",
		source	=>	'grahamgilbert/Make-Recovery-HD',
	}
}