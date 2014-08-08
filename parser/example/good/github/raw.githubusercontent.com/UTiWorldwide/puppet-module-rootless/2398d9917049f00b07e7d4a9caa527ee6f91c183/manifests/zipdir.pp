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

define rootless::zipdir (
  $ensure,
  $zipfile,
  $zipdir = $name
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


  $zipdir_dirname = inline_template('<%= File.dirname(@zipdir) %>')


  if $real_ensure {

    exec {"create-zipfolder-${zipdir}":
      command => "/usr/bin/unzip ${zipfile}",
      cwd     => $zipdir_dirname,
      creates => $zipdir,
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
