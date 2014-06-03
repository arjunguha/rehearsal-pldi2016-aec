class projects::vagrant_puppetmaster (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'vagrant_puppetmaster':
		dir		=>	"${my_sourcedir}/Mine/vagrant-puppetmaster",
		source	=>	'grahamgilbert/vagrant-puppetmaster',
	}
}