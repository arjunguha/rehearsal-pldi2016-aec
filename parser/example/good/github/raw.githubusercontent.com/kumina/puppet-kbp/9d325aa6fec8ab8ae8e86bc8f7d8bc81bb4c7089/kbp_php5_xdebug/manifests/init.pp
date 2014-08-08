class kbp_php5_xdebug {
  include gen_php5::common

  case $lsbdistcodename {
    'lenny':   {
      $file_location = "/usr/lib/php5/20060613/xdebug.so"
      gen_php5::common::config { "zend_extension": value => $file_location; }
    }
    'squeeze': {
      $file_location = "/usr/lib/php5/20090626/xdebug.so"
      gen_php5::common::config { "zend_extension": value => $file_location; }
    }
    'wheezy':  { debug('No longer needed') }
  }

  package { "php5-xdebug":
    notify => Exec["reload-apache2"],
    ensure => latest;
  }

  gen_php5::common::config {
    "xdebug.remote_enable": value => "On";
    "html_errors":          value => "On";
  }
}

class kbp_php5_xdebug::disable {
  package { "php5-xdebug":
    notify => Exec["reload-apache2"],
    ensure => absent;
  }

  gen_php5::common::config {
    "zend_extension":       ensure => absent;
    "xdebug.remote_enable": ensure => absent;
    "html_errors":          ensure => absent;
  }
}
