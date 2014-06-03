class projects::first_boot_pkg (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'first-boot-pkg':
		dir		=>	"${my_sourcedir}/Mine/first-boot-pkg",
		source	=>	'grahamgilbert/first-boot-pkg',
	}
}