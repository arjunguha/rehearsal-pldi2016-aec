class projects::moving_brands (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'moving_brands':
		dir		=>	"${my_sourcedir}/Work/moving-brands",
		source	=>	'pebbleit/Moving-Brands',
	}
}