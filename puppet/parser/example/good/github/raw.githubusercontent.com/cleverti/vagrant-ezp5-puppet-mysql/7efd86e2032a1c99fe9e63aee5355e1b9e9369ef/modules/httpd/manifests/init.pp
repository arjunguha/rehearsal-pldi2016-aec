class httpd {
  $neededpackages = [ "httpd", "php", "php-cli", "php-gd" ,"php-mysql", "php-pear", "php-xml", "php-mbstring", "php-pecl-apc", "php-process", "curl.x86_64", "php-intl.x86_64" ]
  package { $neededpackages:
      ensure => present,
      before => Class['ezpublish']
  } ~>
  file    {'/etc/httpd/conf.d/01.accept_pathinfo.conf':
    ensure  => file,
    content => template('httpd/01.accept_pathinfo.conf.erb'),
    owner   => 'root',
    group   => 'root',
    mode    => '644',
  } ~>
  file    {'/etc/php.d/php.ini':
    ensure  => file,
    content => template('httpd/php.ini.erb'),
    owner   => 'root',
    group   => 'root',
    mode    => '644',
  } 
}