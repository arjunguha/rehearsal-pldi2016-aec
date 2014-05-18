class projects::osx_vm_templates (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	boxen::project { 'osx_vm_templates':
		dir		=>	"${my_sourcedir}/Others/osx-vm-templates",
		source	=>	'timsutton/osx-vm-templates',
	}
}