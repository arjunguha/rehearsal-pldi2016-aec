class projects::crankpkg (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	boxen::project { 'crankpkg':
		dir		=>	"${my_sourcedir}/Mine/buildCrankPkg",
		source	=>	'grahamgilbert/CrankPkg',
	}
}