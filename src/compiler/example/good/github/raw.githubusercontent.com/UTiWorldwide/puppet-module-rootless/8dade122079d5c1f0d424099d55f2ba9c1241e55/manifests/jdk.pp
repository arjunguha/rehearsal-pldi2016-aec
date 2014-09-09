# A class to install jdk as user
# It essentially performes a untar of a specific jdk.tar.gz from
# a directory containing lots of jdk tarballs.
# It can also ensure that jdk is gone.
# It will autodetect architecture and platform

# Usage:

#rootless::jdk { '/opt/app/place/':
#  ensure              => present,
#  jdk_major_version  => '7',
#  jdk_update_version => '25',
#  tarball_directory   => '/big/nfs/mount',
#}
#
#rootless::jdk { '/opt/app/other_place/':
#  ensure            => present,
#  tarball_directory => '/big/nfs/mount',
#  jdk_file         => 'my-special-jdk-tarball.tar.gz',
#  jdk_install_dir  => 'jdk1.7.0_09',    # the directory created by the untar operation
#}
#
#rootless::jdk { '/opt/app/yet_another_place/':
#  ensure           => absent,
#  jdk_install_dir => 'jdk-1.7.0_12',
#}
#
#rootless::jdk { 'my-jdk-install':
#  ensure              => present,
#  jdk_major_version  => '7',
#  jdk_update_version => '25',
#  tarball_directory   => '/big/nfs/mount',
#  install_root        => '/opt/app/best_place',
#}

define rootless::jdk (
  $ensure,
  $tarball_directory = '',
  $jdk_major_version = '',
  $jdk_update_version = '',
  $jdk_file = '',
  $jdk_install_dir= '',
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
      fail('When installing jdk, a tarball_directory must be specified.')
    }
    if $jdk_file != '' {
      if $jdk_install_dir == '' {
        fail('When specifying a tarball via jdk_file, you must also speciy a jdk_install_dir, the directory created by the untar')
      }
    }
  }

  case $::architecture {
    'x86_64': { $jdk_arch = 'x64' }
    'i386':   { $jdk_arch = 'i586' }
    default:  {
      fail("Arch: ${::architecture} not supported, please add it.")
    }
  }

  $jdk_cmp_ver = "${jdk_major_version}u${jdk_update_version}"

  $dwnkernel = downcase($::kernel)

  if $jdk_file == '' {
    $jdk_name = "jdk-${jdk_cmp_ver}-${dwnkernel}-${jdk_arch}.tar.gz"
    $juv_fmt = inline_template('<%= @jdk_update_version.to_s.rjust(2, "0") %>')
    $jdk_create_dir = "jdk1.${jdk_major_version}.0_${juv_fmt}"
  } else {
    $jdk_name = $jdk_file
    $jdk_create_dir = $jdk_install_dir
  }




  if $real_ensure {

    exec {"create-jdk-install-${install_root}":
      command => "/bin/tar xvzf ${tarball_directory}/${jdk_name}",
      cwd     => $install_root,
      creates => "${install_root}/${jdk_create_dir}",
    }

  }
  elsif ! $real_ensure {

    exec {"remove-jdk-install-${install_root}":
      command => "/bin/rm -fr ${jdk_create_dir}",
      cwd     => $install_root,
      onlyif  => "/usr/bin/stat ${install_root}/${jdk_create_dir}",
    }

  }

}
