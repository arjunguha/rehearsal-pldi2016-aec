class ezpublish {
  service { 'httpd':
    ensure => running,
    enable => true,
    before => Class['ezpublish::install'],
    require => [File['/etc/httpd/conf.d/01.accept_pathinfo.conf'], File['/etc/httpd/conf.d/ezp5.conf']]
  } ~>
  exec { "Fix Permissions":
    command => "/bin/chown -R apache:apache /var/www/html/",
    path => "/usr/bin:/usr/sbin:/bin:/usr/local/bin",
    require => Exec['fetch_packages']
  }
}