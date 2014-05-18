define tcpwrappers::allow($ensure = present,
                          $daemon,
                          $client,
                          $except = undef) {
	tcpwrappers::entry { $name:
		ensure => $ensure,
		type   => allow,
		daemon => $daemon,
		client => $client,
		except => $except;
	}
}
