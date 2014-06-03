class drush () {
  # Install drush 4 from package manager
  package { 'drush':
    ensure => installed,
    require => Package['php5-cli'],
  }
  # Install drush 5 manually
  exec { "install-drush-5":
    cwd => '/usr/local/share',
    command => "/usr/bin/curl http://ftp.drupal.org/files/projects/drush-7.x-5.8.tar.gz | /bin/tar -zxvf -; /bin/ln -s /usr/local/share/drush/drush /usr/local/bin/drush5; /usr/local/bin/drush5",
    unless => "/usr/bin/test -f /usr/local/share/drush/drush",
    require => Package['drush']
  }
}
