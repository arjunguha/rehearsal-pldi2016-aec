class apt {
		
	# Translate distribution information to match sources.list file
	$aptsourceslist = $lsbdistdescription ? {
		"Ubuntu 10.04.3 LTS" => "sources.list-10.04",
		"Ubuntu 11.10"   => "sources.list-11.10",
		default  => 'none',
	  }	
	  
	file { 
	"apt-sources-list":
		ensure	=> file,
		path 	=> '/etc/apt/sources.list',
		mode   	=> "0644",
		owner	=> 'root',
		group	=> 'root',
		source	=> "puppet:///modules/apt/${$aptsourceslist}",
		notify	=> Exec['apt-get-update'];
			
	}
	
	exec {
	"apt-get-update":
		command	=> "sudo apt-get update"	
	}
}