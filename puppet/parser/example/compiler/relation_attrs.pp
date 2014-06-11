# simple_relation.pp but instead of arrows we are using attributes

file {'/tmp/dir':
  ensure => directory,
  before => File['/tmp/dir/file1']
}

file {'/tmp/dir/file1':
  ensure => file,
  require => File['/tmp/dir'], #redundant
}

file {'/home/abc/file1':
  ensure => file,
  require => User['abc']
}

user {'abc': ensure => present }

file {'/etc/apache2/httpd.conf':
  ensure => file,
  notify => Service['apache2']
}

service {'apache2': ensure => running}

service {'nginx':
  ensure => running,
  subscribe => File['/etc/nginx/nginx.conf']
}

file {'/etc/nginx/nginx.conf':
  ensure => file,
  notify => Service['nginx']
}
