class php {
  package { [ "php-pear", "php5", "php5-cgi", "php5-curl", "php5-fpm",
              "php5-gd", "php5-imagick", "php5-imap", "php5-intl",
              "php5-mcrypt", "php5-memcache", "php5-ming", "php5-mysql",
              "php5-ps", "php5-pspell", "php5-recode", "php5-snmp",
              "php5-sqlite", "php5-tidy", "php5-xmlrpc", "php5-xsl" ]:
    ensure => latest
  }
  augeas { "Use unix socket":
    require => Package["php5-fpm"],
    lens => "PHP.lns",
    incl => "/etc/php5/fpm/pool.d/www.conf",
    changes => "set /files/etc/php5/fpm/pool.d/www.conf/www/listen '/var/run/php5-fpm.sock'" 
  } ~>
  service { "php5-fpm":
    ensure => running,
    enable => true,
    hasrestart => true
  }
}
