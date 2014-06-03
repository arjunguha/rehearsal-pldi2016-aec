# Class to install Erlang base and nox using .deb package
class erlang-nox-dpkg ($localrepo = '/tmp/repository/archive') {
	
	Exec { path => "/usr/bin:/usr/sbin:/bin" }

	$module = 'erlang-nox-dpkg'
	
	file {
		"/tmp/erlang-base.deb":
			source	=> "puppet:///modules/${module}/erlang-base_1%3a13.b.3-dfsg-2ubuntu2.1_i386.deb";
			
		"/tmp/erlang-nox.deb":
			source	=> "puppet:///modules/${module}/erlang-nox_1%3a13.b.3-dfsg-2ubuntu2.1_i386.deb";
	}
	
	exec {
		'erlang_base':
			require	=> File["/tmp/erlang-base.deb"],
			command	=> "sudo dpkg -l | grep erlang-base | wc -l && sudo dpkg -i /tmp/erlang-base.deb";
			
		'erlang-nox': 
			require	=> [ File["/tmp/erlang-nox.deb"], Exec['erlang_base'] ],
			command	=> "sudo dpkg -l | grep erlang-nox | wc -l && sudo dpkg -i /tmp/erlang-nox.deb";
			
		}

}

