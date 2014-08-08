$present_status = present

file { '/tmp/somefile':
  ensure => $present_status
}
