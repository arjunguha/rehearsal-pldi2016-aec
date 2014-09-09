class php::phpmyadmin () {

  require nginx

  $preseed_path = "/tmp/phpmyadmin.preseed"
  
  file { $preseed_path:
    content => template("php/phpmyadmin.preseed.erb"),
    owner => "root",
    group => "root",
    mode => 0600,
  }
  
  package { "phpmyadmin":
    ensure => latest,
    responsefile => $preseed_path,
  }

  package { "php-db":
    ensure => latest,
  }

  nginx::resource::location { "phpmyadmin":
    ensure   => present,
    location => "/phpmyadmin",
    www_root => "/usr/share/phpmyadmin",
    fastcgi => "127.0.0.1:9000",
    fastcgi_script => "/usr/share/phpmyadmin\$fastcgi_script_name",
  }

  # Create the default location reference for the vHost
  nginx::resource::location {"phpmyadmin":
    ensure         => present,
    location       => "/phpmyadmin",
    proxy          => $proxy,
    proxy_read_timeout => $proxy_read_timeout,
    fastcgi        => $fastcgi,
    fastcgi_params => $fastcgi_params,
    fastcgi_script => $fastcgi_script,
    www_root       => $www_root,
    notify         => Class['nginx::service'],
  }  

}
