define rootless::file(
  $mode    = '0644',
  $content = '',
  $notify  = undef
){

  # this translates it into a file save to write in one file
  # eg.g /etc/httpd/conf.d/app.conf becomes
  # -etc-httpd-conf.d-app.conf
  $tempname = regsubst($name, '/', '-', 'G')

  file { "/var/tmp/${tempname}":
    ensure  => file,
    content => $content,
  }

  exec { "copy-in-${name}":
    command   => "/bin/cat /var/tmp/${tempname} > ${name} && /bin/chmod $mode ${name}",
    subscribe => File["/var/tmp/${tempname}"],
    notify    => $notify,
    unless    => "/usr/bin/[ `/usr/bin/md5sum /var/tmp/${tempname} | /usr/bin/cut -d ' ' -f 1` = `/usr/bin/md5sum ${name} | /usr/bin/cut -d ' ' -f 1` ]"
  }
}

