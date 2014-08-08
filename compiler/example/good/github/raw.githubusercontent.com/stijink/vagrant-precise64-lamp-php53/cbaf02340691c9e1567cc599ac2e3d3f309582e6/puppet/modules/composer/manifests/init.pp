class composer {

  # composer downloaden und zusammensetzen
  exec { 'composer-download':
    command => 'curl -s https://getcomposer.org/installer | php -- --install-dir=/usr/bin',
    require => [Package['curl'],Package['php5']],
    unless  => 'test -f /usr/bin/composer.phar'
  }
}