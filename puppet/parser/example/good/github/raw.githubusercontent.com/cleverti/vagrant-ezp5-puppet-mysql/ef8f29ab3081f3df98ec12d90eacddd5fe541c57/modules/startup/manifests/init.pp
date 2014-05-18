class startup {
    exec    { "add httpd to startup":
      command => "/sbin/chkconfig httpd on",
      path    => "/usr/local/bin/:/bin/",
      require => Package["httpd", "php", "php-cli", "php-gd" ,"php-mysql", "php-pear", "php-xml", "php-mbstring", "php-pecl-apc", "php-process", "curl.x86_64"]
    } ~>
    exec    { "add mysql to startup":
      command => "/sbin/chkconfig --add mysqld",
      path    => "/usr/local/bin/:/bin/",
      require => Package["httpd", "php", "php-cli", "php-gd" ,"php-mysql", "php-pear", "php-xml", "php-mbstring", "php-pecl-apc", "php-process", "curl.x86_64"]
    } ~>
    exec    { "add mysql":
      command => "/sbin/chkconfig mysqld on",
      path    => "/usr/local/bin/:/bin/",
      require => Package["httpd", "php", "php-cli", "php-gd" ,"php-mysql", "php-pear", "php-xml", "php-mbstring", "php-pecl-apc", "php-process", "curl.x86_64"]
    }
}