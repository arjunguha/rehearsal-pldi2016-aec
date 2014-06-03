rootless::jruby { '/opt/app/place/':
  ensure              => present,
  jruby_version       => '1.7.1',
  tarball_directory   => '/big/nfs/mount',
}

rootless::jruby { '/opt/app/other_place/':
  ensure             => present,
  tarball_directory  => '/big/nfs/mount',
  jruby_file         => 'my-special-jruby-tarball.tar.gz',
  jruby_install_dir  => 'jruby-1.7.1',    # the directory created by the untar operation
}

rootless::jruby { '/opt/app/yet_another_place/':
  ensure            => absent,
  jruby_install_dir => 'jruby-1.6.6',
}

rootless::jruby { 'my-jruby-install':
  ensure               => present,
  jruby_version        => '1.6.6',
  tarball_directory    => '/big/nfs/mount',
  install_root         => '/opt/app/best_place',
}
