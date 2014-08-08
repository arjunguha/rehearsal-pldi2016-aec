define tcpwrappers::deny($ensure = present,
                         $daemon,
                         $client,
                         $except = undef) {
	tcpwrappers::entry { $name:
		ensure => $ensure,
		type   => deny,
		daemon => $daemon,
		client => $client,
		except => $except;
	}
}
