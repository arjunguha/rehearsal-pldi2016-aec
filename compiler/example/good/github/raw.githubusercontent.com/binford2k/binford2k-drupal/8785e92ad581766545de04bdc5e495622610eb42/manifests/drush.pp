class drupal::drush (
  $docroot    = $drupal::docroot,
  $version    = $drupal::drushversion,
  $installdir = '/usr/local/share',
) {
  # When drush7 gets packaged, drop this crap

  # adding support for new drush release location

  if versioncmp($version, '5.9.9') > 0 {
    $download_url =  "https://github.com/drush-ops/drush/archive/${version}.tar.gz"
    $unpackdir = "drush-$version"
  } else {
    $download_url = "http://ftp.drupal.org/files/projects/drush-${version}.tar.gz"
    $unpackdir = 'drush'
  }
  if $drupal::installtype == 'remote' {
    exec { 'install drush':
      command => "/bin/tar -xf /tmp/drush-${version}.tar.gz -C ${installdir} && rm /tmp/drush-${version}.tar.gz",
      onlyif  => "/usr/bin/wget ${download_url} -O /tmp/drush-${version}.tar.gz",
      creates => "${installdir}/${unpackdir}",
    }
  } else {
    file { "/tmp/drush-${version}.tar.gz":
      ensure => file,
      source => "puppet:///modules/drupal/drush-${version}.tar.gz",
      before => Exec['install drush'],
    }
    exec { 'install drush':
      command => "/bin/tar -xf /tmp/drush-${version}.tar.gz -C ${installdir}",
      creates => "${isntalldir}/${unpackdir}",
    }
  }

  file { '/usr/local/bin/drush':
    ensure  => symlink,
    target  => "${installdir}/${unpackdir}/drush",
    require => Exec['install drush'],
  }

  file { '/etc/drush':
    ensure => directory,
  }

  file { '/etc/drush/drushrc.php':
    ensure  => file,
    content => template('drupal/drushrc.php.erb'),
  }
}

