class haproxy {

	package  {
	"haproxy":
		ensure 	=> present;
	}
	
	file {
		
		'/etc/haproxy/haproxy.cfg':
		require	=> Package["haproxy"],
		ensure	=> present,
		content => template('haproxy/haproxy.cfg.erb'),
		before	=> Exec['restart-haproxy'];
	}
	
	exec {
		# stops and starts process
		'restart-haproxy':
		command	=> '/usr/bin/pkill haproxy ; /usr/sbin/haproxy -f /etc/haproxy/haproxy.cfg',
	}
	

}