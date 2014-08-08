define chroot::root (
  $yum,
  $version   = 1,
  $rpms      = '',
  $rpms_suid = 'rpm',
  ) {

  include chroot

  $base_dir = "${chroot::base_dir}/${name}-v${version}"
  $root_dir = "${base_dir}/root"
  $chroot_tool = "/usr/sbin/chroot-tool -c /etc/chroot-tool/tool-${name}.cfg"

  ##############################################
  # chroot-tool configuration
  ##############################################

  file { "/etc/chroot-tool/tool-$name.cfg":
    content => template('chroot/tool.cfg.erb'),
    require => Package["chroot-tool"],
    before  => Exec["chroot-create-$name"],
  }

  file { "/etc/chroot-tool/yum-$name.conf":
#    source  => $yum,
    source  => "puppet:///modules/chroot/yum-$name.conf",
    require => Package["chroot-tool"],
    before  => Exec["chroot-create-$name"],
  }

  ##############################################
  # Install chroot
  ##############################################

  # Create /chroot/$name-v$version/root directory
  exec { "chroot-create-$name":
    command   => "$chroot_tool create",
    creates   => $root_dir,
  }

  # Install chroot
  exec { "chroot-install-$name":
    command   => "$chroot_tool install @core redhat-lsb $rpms && touch $base_dir/.install",
    creates   => "$base_dir/.install",
    require   => Exec["chroot-create-$name"],
    timeout   => 3600,
  }

  # Secure chroot, removing set[ug]id bits
  exec { "chroot-secure-$name":
    command   => "$chroot_tool secure && touch $base_dir/.secure",
    creates   => "$base_dir/.secure",
    require   => Exec["chroot-install-$name"],
  }

  # After securing, install RPMs for things we need to really be setuid
  exec { "chroot-install-suid-$name":
    command   => "$chroot_tool install $rpms_suid && touch $base_dir/.install.suid",
    creates   => "$base_dir/.install.suid",
    require   => Exec["chroot-secure-$name"],
    timeout   => 3600,
  }

  ##############################################
  # Mounts, bind and otherwise
  #   TODO: Make this block a cluster-specific thing?
  ##############################################

  chroot::mount { $root_dir:
    require => Exec["chroot-install-suid-$name"],
  }

  ##############################################
  # Final tasks
  ##############################################

  # Symlink from /chroot/$name to current version of root
  file { "${chroot::base_dir}/$name":
    ensure  => link,
    target  => $root_dir,
    require => Chroot::Mount[$root_dir],
  }

#  # Register with autofs
#  autofs::add_map { "autofs for chroot ${base_dir}":
#    map        => '/etc/auto.cvmfs',
#    mountpoint => "${base_dir}/root/cvmfs",
#    require => Chroot::Mount[$root_dir],
#  }

}
