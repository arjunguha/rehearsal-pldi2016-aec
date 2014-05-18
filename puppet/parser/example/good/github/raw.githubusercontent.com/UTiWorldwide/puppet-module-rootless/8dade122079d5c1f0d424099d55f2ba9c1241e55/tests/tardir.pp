rootless::tardir { '/opt/app/place/folder':
  ensure  => absent,
  tarfile => '/big/nfs/mount/tar.tar.gz'
}

rootless::tardir { '/opt/app/other_place/folder':
  ensure  => present,
  tarfile => '/big/nfs/mount/tar.tar.gz'
}

