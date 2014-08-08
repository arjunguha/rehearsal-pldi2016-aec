# A class to install jruby as user
# It essentially performes a untar of a specific jruby.tar.gz from
# a directory containing lots of jruby tarballs.
# It can also ensure that jruby is gone.
# It will autodetect architecture and platform

# Usage:

#rootless::jruby { '/opt/app/place/':
#  ensure              => present,
#  jruby_version       => '1.7.1',
#  tarball_directory   => '/big/nfs/mount',
#}
#
#rootless::jruby { '/opt/app/other_place/':
#  ensure             => present,
#  tarball_directory  => '/big/nfs/mount',
#  jruby_file         => 'my-special-jruby-tarball.tar.gz',
#  jruby_install_dir  => 'jruby-1.7.1',    # the directory created by the untar operation
#}
#
#rootless::jruby { '/opt/app/yet_another_place/':
#  ensure            => absent,
#  jruby_install_dir => 'jruby-1.6.6',
#}
#
#rootless::jruby { 'my-jruby-install':
#  ensure               => present,
#  jruby_version        => '1.6.6',
#  tarball_directory    => '/big/nfs/mount',
#  install_root         => '/opt/app/best_place',
#}


define rootless::jruby (
  $ensure,
  $tarball_directory = '',
  $jruby_version = '',
  $jruby_file = '',
  $jruby_install_dir= '',
  $install_root = $name
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
    if $tarball_directory == '' {
      fail('When installing jruby, a tarball_directory must be specified.')
    }
    if $jruby_file != '' {
      if $jruby_install_dir == '' {
        fail('When specifying a tarball via jruby_file, you must also speciy a jruby_install_dir, the directory created by the untar')
      }
    }
  }



  if $jruby_file == '' {
    $jruby_name = "jruby-bin-${jruby_version}.tar.gz"
    $jruby_create_dir = "jruby-${jruby_version}"
  } else {
    $jruby_name = $jruby_file
    $jruby_create_dir = $jruby_install_dir
  }




  if $real_ensure {

    exec {"create-jruby-install-${install_root}":
      command => "/bin/tar xvzf ${tarball_directory}/${jruby_name}",
      cwd     => $install_root,
      creates => "${install_root}/${jruby_create_dir}",
    }

  }
  elsif ! $real_ensure {

    exec {"remove-jruby-install-${install_root}":
      command => "/bin/rm -fr ${jruby_create_dir}",
      cwd     => $install_root,
      onlyif  => "/usr/bin/stat ${install_root}/${jruby_create_dir}",
    }

  }

}
