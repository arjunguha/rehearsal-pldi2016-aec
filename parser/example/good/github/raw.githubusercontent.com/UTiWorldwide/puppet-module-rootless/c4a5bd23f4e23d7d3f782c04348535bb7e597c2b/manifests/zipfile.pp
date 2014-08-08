# A type to unzip a zipfile at a location, creating
# a directory

# Usage

#rootless::zipdir { '/opt/app/place/folder':
#  ensure  => absent,
#  zipfile => '/big/nfs/mount/zipfile.zip'
#}
#
#rootless::zipdir { '/opt/app/other_place/folder':
#  ensure  => present,
#  zipfile => '/big/nfs/mount/zipfill.zip'
#}

define rootless::zipfile (
  $ensure,
  $zipdir, #This is the location where files will be unzipped
  $creates, #If this file exists on the system, the unzip will be skipped.
  $zipfile = $name
){

  case $ensure {
    true: {
      $real_ensure = true
    }
    /present|true/: {
      $real_ensure = true
    }
    false: {
      $real_ensure = false
    }
    /absent|false/: {
      $real_ensure = false
    }
    default: {
      fail("ensure: ${ensure} not supported.")
    }
  }


  if $real_ensure {

    exec {"create-zipfolder-${zipfile}":
      command => "/usr/bin/unzip ${zipfile}",
      cwd     => $zipdir,
      creates => $creates,
    }

  }
  elsif ! $real_ensure {

    exec {"remove-zipfolder-${zipdir}":
      command => "/bin/rm -rf ${zipdir}",
      cwd     => $zipdir_dirname,
      onlyif  => "/usr/bin/stat ${zipdir}",
    }

  }


}
