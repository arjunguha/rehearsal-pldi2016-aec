file { '/tmp/dir':
  ensure => directory
}

->

file { '/tmp/dir/file1':
  ensure => file,
  content => "Some Content"
}
