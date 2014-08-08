class projects::grahamgilbert_mac_facts (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'grahamgilbert_mac_facts':
		dir		=>	"${my_sourcedir}/Mine/grahamgilbert-mac_facts",
		source	=>	'grahamgilbert/grahamgilbert-mac_facts',
	}
}