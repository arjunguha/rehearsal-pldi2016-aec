class php::nginx ($packages = [ "php5-fpm", "php5-cgi" ],
                  $www_root = "/var/www",
                  $fastcgi = "127.0.0.1:9000"){
  
  package { $packages:
    ensure => latest,
  }

  # remove apache2 packages that are auto-installed on ubuntu
  $apache_packages = [ "apache2.2-common", "apache2.2-bin", "apache2-utils" ]
  package { $apache_packages:
    ensure => absent,
  }
  
  nginx::resource::vhost { $name:
    ensure   => present,
    www_root => $www_root,
    fastcgi => $fastcgi,
    fastcgi_index => "index.php",
    fastcgi_script => "$www_root\$fastcgi_script_name",
  }

}
