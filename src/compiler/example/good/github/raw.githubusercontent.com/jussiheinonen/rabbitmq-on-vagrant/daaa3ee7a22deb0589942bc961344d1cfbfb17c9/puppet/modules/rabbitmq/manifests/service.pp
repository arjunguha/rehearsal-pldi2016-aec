class rabbitmq::service ($enabled = false) {
	
	include rabbitmq
	
		service {
		'rabbitmq-server':
			ensure		=> $enabled,
			hasrestart	=> true,
			subscribe	=> File['/etc/rabbitmq/rabbitmq.config'];
		}
}