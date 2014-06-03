class rabbit_install {
  class { 'rabbitmq::repo::apt':
    pin    => 1000,
    before => Class['rabbitmq::server']
  }

  exec { "apt-get-update2":
    command     => "/usr/bin/apt-get update",
  }

  class { 'rabbitmq::server':
    version => '2.7.1-1',
    port              => '5673',
    delete_guest_user => true,
  }

  file { '/var/lib/rabbitmq/.erlang.cookie':
    source => ['/tmp/vagrant-puppet/manifests/files/erlang_cookie'],
    owner => "rabbitmq",
    group => "rabbitmq",
    mode => "400",
    before => Class['rabbitmq::service']
  }
}