class httpd::apc {
    $neededpackages = [ "php-devel", "httpd-devel", "pcre-devel.x86_64", "php-pecl-apc.x86_64" ]
    package { $neededpackages:
      ensure => installed
    } ~>
    file    {'/etc/php.d/apc.ini':
      ensure  => file,
      content => template('httpd/apc.ini.erb'),
    }
}