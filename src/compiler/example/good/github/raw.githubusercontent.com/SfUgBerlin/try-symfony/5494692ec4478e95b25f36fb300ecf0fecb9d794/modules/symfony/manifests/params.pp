class symfony::params {

	$root_dir_name = $root_dir_name ? {
        	 "" => "symfony",
    	default => $root_dir_name,
  	}
  	
  	$root_dir_path = $root_dir_path ? {
        	 "" => "/tmp",
    	default => $root_dir_path,
  	}
  	
  	$root_dir = $root_dir ? {
        	 "" => "${root_dir_path}/${root_dir_name}",
    	default => $root_dir,
  	}
  	
  	$download_url = $download_url ? {
  		"" => "http://github.com/symfony/symfony-standard.git",
  		default => $download_url,
  	}
  	
    $www_project_path = $www_project_path ? {
        "" => "/var/www/symfony",
        default => "$www_project_path"
    }
  	
}