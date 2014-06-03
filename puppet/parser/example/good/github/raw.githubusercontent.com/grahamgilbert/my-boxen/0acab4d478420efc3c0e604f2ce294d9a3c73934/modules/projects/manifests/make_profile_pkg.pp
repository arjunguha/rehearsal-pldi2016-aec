class projects::make_profile_pkg (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
        boxen::project { 'make_profile_pkg':
		dir		=>	"${my_sourcedir}/Others/make-profile-pkg",
		source	=>	'timsutton/make-profile-pkg',
	}
    
}