class riak_install {
  exec { "dl_riak":
    cwd => "/var/tmp",
    command => "wget http://downloads.basho.com/riak/riak-1.0.2/riak_1.0.2-1_amd64.deb",
    creates => "/var/tmp/riak_1.0.2-1_amd64.deb",
    timeout => 600,
    path => ["/usr/bin", "/usr/sbin"],
    before  => Exec["install_riak"],
  }
  exec { "install_riak":
    cwd => "/var/tmp",
    command => "dpkg -i riak_1.0.2-1_amd64.deb",
    creates => "/var/lib/dpkg/info/riak.list",
    path => ['/usr/local/sbin','/usr/local/bin','/usr/sbin', '/usr/bin', '/sbin', '/bin', '/opt/ruby/bin/'],
  }

  file { '/var/lib/riak/.erlang.cookie':
    source => ['/tmp/vagrant-puppet/manifests/files/erlang_cookie'],
    owner => "riak",
    group => "riak",
    mode => "400",
    before => Service['riak']
  }

  service { 'riak':
    ensure => running
  }
}
