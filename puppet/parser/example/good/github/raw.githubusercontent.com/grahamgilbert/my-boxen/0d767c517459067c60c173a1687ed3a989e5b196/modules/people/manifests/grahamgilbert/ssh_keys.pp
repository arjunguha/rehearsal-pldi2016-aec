class people::grahamgilbert::ssh_keys (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	file { "/Users/${::luser}/.ssh/ggmbpkey.pem":
		source => "/Users/${::luser}/Dropbox/Config/AWS Keys/Personal/ggmbpkey.pem",
        owner => "${::luser}",
        mode => '0600',
        require => Repository['oh-my-zsh'],
	}
    
	file { "/Users/${::luser}/.ssh/pebble.pem":
		source => "/Users/${::luser}/Dropbox/Config/AWS Keys/Work/pebble.pem",
        owner => "${::luser}",
        mode => '0600',
        require => Repository['oh-my-zsh'],
	}
    
	file { "/Users/${::luser}/.ssh/id_rsa":
		source => "/Users/${::luser}/Dropbox/Config/SSH Keys/id_rsa",
        owner => "${::luser}",
        mode => '0600',
	}
    
	file { "/Users/${::luser}/.ssh/id_rsa.pub":
		source => "/Users/${::luser}/Dropbox/Config/SSH Keys/id_rsa.pub",
        owner => "${::luser}",
        mode => '0644',
	}
	
	file { "/Users/${::luser}/.ssh":
		ensure => directory,
	}
	
}