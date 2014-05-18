class chroot (
  $base_dir = params_lookup( 'base_dir' ),
  ) inherits chroot::params {

  # FIXME: Duplicate definition of chroot5
  package { 'chroot-tool':
    ensure  => present,
  }

  # FIXME: Duplicate definition of chroot5
  # Create /chroot directory
  #file { $base_dir:
  #  ensure => directory,
  #  path   => $base_dir
  #}

}
