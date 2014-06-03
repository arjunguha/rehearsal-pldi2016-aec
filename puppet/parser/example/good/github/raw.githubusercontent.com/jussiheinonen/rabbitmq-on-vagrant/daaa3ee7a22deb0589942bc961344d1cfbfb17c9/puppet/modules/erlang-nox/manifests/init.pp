class erlang-nox {
	
	require	apt
	
	# Translate distribution information to match sources.list file
	$erlangpkg = $lsbdistdescription ? {
		"Ubuntu 10.04.3 LTS" => "erlang-nox",
		"Ubuntu 11.10"   => "erlang-nox",
		default  => 'erlang-nox',
	  }
	
	
	package  {
		"${erlangpkg}":
			ensure 	=> present;
	}

}	