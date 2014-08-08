define aegir::module($version, $user = 'aegir', $location = '/var/aegir/hostmaster-6.x-1.9/sites/all/modules') {
  exec { "aegir-download-${name}":
    command => "/bin/su aegir -c \"/usr/bin/drush @hostmaster dl ${name}-${version}\"",
    creates => "/var/aegir/hostmaster-6.x-1.9/sites/all/modules/${name}",
    require => Package['aegir'],
  }
}

