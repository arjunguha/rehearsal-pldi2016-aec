class drupal::package::bundled (
  $installroot = $drupal::installroot,
  $docroot     = $drupal::docroot,
  $version     = $drupal::drupalversion,
  $source      = undef,
) {

  if $source == undef {
    $real_source =  "puppet:///modules/drupal/drupal-${version}.tar.gz"
  } else {
    $real_source = $source
  }

  $php_modules = $osfamily ? {
    'RedHat' =>  ['gd', 'pdo', 'xml'],
    default  =>  ['gd', 'mbstring', 'pdo', 'xml'],
  }

  php::module { $php_modules:
    ensure => installed,
    before => Exec['install drupal'],
  }

  file { "/tmp/drupal-${version}.tar.gz":
    ensure => file,
    source => $real_source,
    before => Exec['install drupal'],
  }


  exec { 'install drupal':
    command => "/bin/tar --no-same-owner -xf /tmp/drupal-${version}.tar.gz",
    cwd     => $installroot,
    creates => "${installroot}/drupal-${version}",
    before  => File[$docroot],
  }
  file { $docroot:
    ensure => symlink,
    target => "drupal-${version}",
  }
}
