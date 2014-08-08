class projects::crypt_server (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	#include python
	
	boxen::project { 'crypt-server':
		dir		=>	"${my_sourcedir}/Mine/crypt-server",
		source	=>	'grahamgilbert/Crypt-Server',
	}
	
	
	##One day I'll get virtualenvs working
	
	#if !defined(File["${my_homedir}/virtualenvs"]){
	#	file { "${my_homedir}/virtualenvs":
	#		ensure => directory,
	#	}
	#}
	
	#python::venv::isolate { "${my_homedir}/virtualenvs/crypt-server":
	#  requirements => "${my_sourcedir}/Mine/crypt-server/setup/requirements.txt",
	#  require	=> Boxen::Project['crypt_server'],
	#}
}