class rabbitmq::clustermember {
	exec {
		'/usr/sbin/rabbitmqctl stop_app':
			require	=> Exec['rabbit-start'];
		'/usr/sbin/rabbitmqctl reset':
			require	=> Exec['/usr/sbin/rabbitmqctl stop_app'];
		"/usr/sbin/rabbitmqctl cluster  rabbit@${rabbitcoordinator}":
			require	=> Exec['/usr/sbin/rabbitmqctl reset'];
		'/usr/sbin/rabbitmqctl start_app':
			require	=> Exec["/usr/sbin/rabbitmqctl cluster  rabbit@${rabbitcoordinator}"];								
	}
}