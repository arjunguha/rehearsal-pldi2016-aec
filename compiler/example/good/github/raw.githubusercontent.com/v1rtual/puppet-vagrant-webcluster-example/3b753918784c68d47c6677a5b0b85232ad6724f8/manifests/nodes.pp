node default {
  package { "default-packages":
    ensure => installed,
    name => [
      "puppet",
      "git-core"
    ]
  }
  include ntp

  file { '/root/.gemrc':
    source => ["/tmp/vagrant-puppet/manifests/files/gemrc"],
    owner => "root",
    group => "root"
  }
}

node "web1.local", "web2.local" inherits default {
    $server_name="33.33.33.31"
    include web
}

node "lb.local" inherits default {
    $server_name="33.33.33.30"
    include lb
}
