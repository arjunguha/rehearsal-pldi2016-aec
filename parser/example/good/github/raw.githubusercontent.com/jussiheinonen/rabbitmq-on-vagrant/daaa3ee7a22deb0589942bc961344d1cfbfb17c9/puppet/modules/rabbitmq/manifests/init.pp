class rabbitmq ($version = '2.7.1', $enabled = false) {
	require erlang-nox
	class { 'rabbitmq::service': enabled => $enabled }

	$installer = "rabbitmq-server_${version}-1_all.deb"
	
	# Resource defaults
	File { owner => "0", group => "0", mode  => "0644", notify => Exec['rabbit-start'] }
	Exec { path => "/usr/bin:/usr/sbin:/bin" }
	
	# Include class 
	if $rabbitcoordinator != $hostname {
		include rabbitmq::clustermember
	}
	else {
		notify {
			"I am the RabbitMQ coordinator, awaiting for members to join in":
		}		
	}	
	
	# RabbitMQ installer package for Debian. 
	file {
	"/tmp/${installer}":
		source  => "puppet:///modules/rabbitmq/${installer}";
		
	'/etc/rabbitmq/rabbitmq.config':
		owner => 'rabbitmq', 
		group => 'rabbitmq',
		mode  => 0755,
		require	=> Exec['rabbit-stop'],
		source	=> 'puppet:///modules/rabbitmq/rabbitmq.config.example';
	
	'/var/lib/rabbitmq/.erlang.cookie':
		owner => 'rabbitmq', 
		group => 'rabbitmq',
		mode  => 0400,
		require	=> Exec['rabbit-stop'],
		source	=> 'puppet:///modules/rabbitmq/erlang.cookie';
	
	'/etc/hosts':
		content => template('rabbitmq/hosts.erb'),			
	}

	exec {
		'install-deb':
			command => "sudo dpkg -i /tmp/${installer}",
			creates => "/usr/lib/rabbitmq/bin/rabbitmq-server",
			require => File["/tmp/${installer}"];
		'rabbit-stop':
			require	=> Exec['install-deb'],
			command	=> '/etc/init.d/rabbitmq-server stop';
		'rabbit-start':
			require	=> Exec['rabbit-stop'],
			command	=> '/etc/init.d/rabbitmq-server start';

	}
	
	
}