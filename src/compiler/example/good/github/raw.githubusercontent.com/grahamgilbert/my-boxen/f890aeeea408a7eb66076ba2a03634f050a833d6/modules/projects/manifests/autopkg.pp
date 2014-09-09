class projects::autopkg (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	
	
	boxen::project { 'autopkg':
		dir		=>	"${my_sourcedir}/Others/autopkg",
		source	=>	'autopkg/autopkg',
	}
    
    # config for AutoPkg
	boxen::osx_defaults { 'autopkg Munki repository':
		  ensure => present,
		  domain => 'com.github.autopkg',
		  key    => 'MUNKI_REPO',
		  value  => '/Volumes/Munki',
	}
    
    exec {'install autopkg server deamon':
        command => "${my_sourcedir}/Others/autopkg/Scripts/install.sh",
        creates => '/Library/LaunchDaemons/com.github.autopkg.autopkgserver.plist',
        require => Boxen::Project['autopkg'],
        user    => root,
        cwd     => "${my_sourcedir}/Others/autopkg",
    }
}