rootless::jdk { '/opt/app/place/':
  ensure              => present,
  jdk_major_version  => '7',
  jdk_update_version => '25',
  tarball_directory   => '/big/nfs/mount',
}

rootless::jdk { '/opt/app/other_place/':
  ensure            => present,
  tarball_directory => '/big/nfs/mount',
  jdk_file         => 'my-special-jdk-tarball.tar.gz',
  jdk_install_dir  => 'jdk1.7.0_09',    # the directory created by the untar operation
}

rootless::jdk { '/opt/app/yet_another_place/':
  ensure           => absent,
  jdk_install_dir => 'jdk-1.7.0_12',
}

rootless::jdk { 'my-jdk-install':
  ensure              => present,
  jdk_major_version  => '7',
  jdk_update_version => '25',
  tarball_directory   => '/big/nfs/mount',
  install_root        => '/opt/app/best_place',
}
