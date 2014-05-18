#
# == Definition: selinux::module::redhat
#
# This definition builds a binary SELinux module with the Makefile provided by
# the selinux-policy-devel or selinux-policy package.
# It should only be called ba the selinux::module definition, in case of
# RedHat osfamily.
#
# Parameters:
#
# - *name*: the name of the SELinux module
# - *workdir*: where the module source and binary files are stored. Defaults to
#   "/etc/puppet/selinux" (not used here, yet ?)
# - *dest*: where the binary module must be copied. Defaults to
#   "/usr/share/selinux/targeted/"
# - *content*: inline content or template of the module source
# - *source*: file:// or puppet:// URI of the module source file
#
#
define selinux::module::redhat (
  $ensure=present,
  $dest='/usr/share/selinux/targeted/',
  $content=undef,
  $source=undef,
  $load=true,
) {

  case $ensure {
    present: {
      file { "${dest}/${name}.te":
        ensure  => present,
        content => $content,
        source  => $source,
        notify  => Exec["build selinux policy package ${name} if .te changed"],
      }
    
      $build_reqs = $lsbmajdistrelease  ? {
        '5'     => [File["${dest}/${name}.te"], Package['checkpolicy'], Package ['selinux-policy-devel']],
        default => [File["${dest}/${name}.te"], Package['checkpolicy']],
      }
      $make_cmd = "make -f /usr/share/selinux/devel/Makefile ${name}.pp"
    
      # Module building needs to happen in two cases that cannot be defined in a single Exec
      exec { "build selinux policy package ${name} if .te changed":
        cwd         => $dest,
        command     => $make_cmd,
        require     => $build_reqs,
        refreshonly => true,
      }
      exec { "build selinux policy package ${name} if .pp missing":
        cwd     => $dest,
        command => $make_cmd,
        creates => "${dest}/${name}.pp",
        require => flatten([ $build_reqs, Exec["build selinux policy package ${name} if .te changed"] ]),
      }
    
      if $load {
        selmodule { $name:
          ensure      => present,
          syncversion => true,
          require     => Exec["build selinux policy package ${name} if .pp missing"],
        }
      }
    }
    absent: {
      file {["${dest}/${name}.te",
             "${dest}/${name}.if",
             "${dest}/${name}.fc",
             "${dest}/${name}.pp"]:
        ensure => absent,
      }

      if $load {
        selmodule { $name:
          ensure => absent,
        }
      }
    }
    default: { fail "$ensure must be 'present' or 'absent'" }
  }


}
