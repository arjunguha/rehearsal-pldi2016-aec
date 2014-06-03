# A type to untar a tarfile at a location, creating
# a directory

# Usage

#rootless::tardir { '/opt/app/place/folder':
#  ensure  => absent,
#  tarfile => '/big/nfs/mount/tar.tar.gz'
#}
#
#rootless::tardir { '/opt/app/other_place/folder':
#  ensure  => present,
#  tarfile => '/big/nfs/mount/tar.tar.gz'
#}

define rootless::tardir (
  $ensure,
  $tarfile,
  $tardir = $name
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


  $tardir_dirname = inline_template('<%= File.dirname(@tardir) %>')


  if $real_ensure {

    exec {"create-tarfolder-${tardir}":
      command => "/bin/tar xvzf ${tarfile}",
      cwd     => $tardir_dirname,
      creates => $tardir,
    }

  }
  elsif ! $real_ensure {

    exec {"remove-tarfolder-${tardir}":
      command => "/bin/rm -rf ${tardir}",
      cwd     => $tardir_dirname,
      onlyif  => "/usr/bin/stat ${tardir}",
    }

  }


}
