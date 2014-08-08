class people::grahamgilbert::homebrew (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	homebrew::tap { 'homebrew/binary': } ->
    homebrew::tap { 'timsutton/formulae': }
	
}