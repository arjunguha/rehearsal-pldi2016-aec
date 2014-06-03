class projects::instadmg_catalogs (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'instadmg_catalogs':
		dir		=>	"${my_sourcedir}/Mine/InstaDMG-Catalogs",
		source	=>	'grahamgilbert/InstaDMG-Catalogs',
	}
}