rootless::zipdir { '/opt/app/place/folder':
  ensure  => absent,
  zipfile => '/big/nfs/mount/zipfile.zip'
}

rootless::zipdir { '/opt/app/other_place/folder':
  ensure  => present,
  zipfile => '/big/nfs/mount/zipfill.zip'
}
