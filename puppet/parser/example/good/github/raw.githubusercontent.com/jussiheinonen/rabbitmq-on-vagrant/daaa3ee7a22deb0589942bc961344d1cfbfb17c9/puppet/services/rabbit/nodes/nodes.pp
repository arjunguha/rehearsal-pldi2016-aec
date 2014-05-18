node /^rabbitmq-server.*/ {
	require initialise
	class { 'rabbitmq': version => '2.7.1', enabled => true }

}

node /^haproxy.*/ {
	require initialise
	include haproxy	
}
