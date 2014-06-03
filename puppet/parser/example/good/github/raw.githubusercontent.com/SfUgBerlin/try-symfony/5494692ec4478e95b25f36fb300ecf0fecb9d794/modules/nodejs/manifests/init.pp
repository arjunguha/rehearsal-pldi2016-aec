class nodejs ( $version, $logoutput = 'on_failure' ) {

  package { 'curl':
    ensure => present,
  }
  
  package { 'libssl-dev':
    ensure => present,
  }
  
  package { 'build-essential':
    ensure => present,
  }
  
  #nave installation depends on phython-core
  package { 'bzr':
    ensure => present,
  }

  # use nave, yo
  exec { 'nave' :
    command     => "bash -c \"\$(curl -s 'https://raw.github.com/isaacs/nave/master/nave.sh') usemain $version \"",
    path        => [ "/usr/local/bin", "/bin" , "/usr/bin" ],
    require     => [ Package[ 'curl' ], Package[ 'libssl-dev' ], Package[ 'build-essential' ] ],
    environment => [ 'HOME=""', 'PREFIX=/usr/local/lib/node' ],
    logoutput   => $logoutput,
    timeout => 0,
  }

}

