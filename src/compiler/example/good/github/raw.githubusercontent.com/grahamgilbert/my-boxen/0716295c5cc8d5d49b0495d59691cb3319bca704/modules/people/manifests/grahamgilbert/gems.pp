class people::grahamgilbert::gems (
	$my_homedir   = $people::grahamgilbert::params::my_homedir,
  	$my_sourcedir = $people::grahamgilbert::params::my_sourcedir,
  	$my_username  = $people::grahamgilbert::params::my_username
	){
	
	ruby::gem { 'bundler for 1.9.3':
		gem  => 'bundler',
		ruby => '1.9.3',
	}
	
	ruby::gem { 'puppet-lint for 1.9.3':
		gem  => 'puppet-lint',
		ruby => '1.9.3',
	}
	
	ruby::gem { 'librarian-puppet for 1.9.3':
		gem  => 'librarian-puppet',
		ruby => '1.9.3',
	}
	
	ruby::gem { 'rspec-puppet for 1.9.3':
		gem  => 'rspec-puppet',
		ruby => '1.9.3',
	}
	
	ruby::gem { 'puppetlabs_spec_helper for 1.9.3':
		gem	 => 'puppetlabs_spec_helper',
		ruby => '1.9.3',
	}
	
	ruby::gem { 'puppet for 1.9.3':
		gem	 => 'puppet',
		ruby => '1.9.3',
	}
	
}