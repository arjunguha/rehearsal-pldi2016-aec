class upgrade_distro {

  exec { 'aptgetupdate':
    command => '/usr/bin/apt-get -y update',
    user    => 'root',
    timeout => 9999,
  }

  exec { '/usr/bin/apt-get -y upgrade':
    user    => 'root',
    require => Exec['aptgetupdate'],
    timeout => 9999,
  }

}
