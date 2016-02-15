file { '/mydir': 
  ensure => 'directory'
}
file { '/mydir/myfile':
  ensure => 'file'
}