class php::install (
  $packages = ["php5-cli", "php5-dev", "php5-curl", "php5-memcache", "php5-common", "php5-mysql", 
               "php-pear", "php5-gd", "php5-imagick", "php5-imap", "php5-mcrypt", "php-apc",
               "php5-ming", "php5-ps", "php5-pspell", "php5-recode", "php5-snmp", "php5-sqlite", 
               "php5-tidy", "php5-xsl"]){
               
  package { $packages:
    ensure => latest,
  }

}
