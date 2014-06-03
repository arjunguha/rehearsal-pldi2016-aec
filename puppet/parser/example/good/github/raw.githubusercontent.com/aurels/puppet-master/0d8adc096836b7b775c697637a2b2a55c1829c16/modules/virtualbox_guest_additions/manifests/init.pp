class virtualbox_guest_additions {

  package { 'module-assistant': ensure => present }

  exec { 'm-a':
    command => '/bin/echo "Y" | /usr/bin/m-a prepare',
    user    => 'root',
    timeout => 9999,
    require => [
      Package['build-essential'],
      Package['module-assistant'],
    ]
  }

  exec { '/etc/init.d/vboxadd setup':
    user    => 'root',
    require => Exec['m-a'],
    timeout => 9999,
  }

}
