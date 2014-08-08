define chroot::mount (
) {

  chroot::do_bind { "$name/dev":               dev  => '/dev' }
  chroot::do_bind { "$name/proc":              dev  => '/proc' }
  chroot::do_bind { "$name/sys":               dev  => '/sys' }
  chroot::do_bind { "$name/tmp":               dev  => '/tmp' }
  chroot::do_bind { "$name/var/tmp":           dev  => '/var/tmp' }
  chroot::do_bind { "$name/var/lib/sss":       dev  => '/var/lib/sss' }
  chroot::do_bind { "$name/etc/grid-security": dev  => '/etc/grid-security' }
  chroot::do_bind { "$name/etc/group":         dev  => '/etc/group' }
  chroot::do_bind { "$name/etc/passwd":        dev  => '/etc/passwd' }
  chroot::do_bind { "$name/etc/hosts":         dev  => '/etc/hosts' }
  chroot::do_bind { "$name/etc/nsswitch.conf": dev  => '/etc/nsswitch.conf' }

  # These need pre-created targets
  chroot::do_bind { "$name/etc/resolv.conf":   dev  => '/etc/resolv.conf',   ensure => 'file' }

  ##################################################
  # Cluster-specific mounts
  # TODO: Move the cluster-specific mounts outside?
  ##################################################
  #chroot::do_bind { "$name/work":              dev  => '/lustre/work',       ensure => 'directory' }
  #chroot::do_bind { "$name/util":              dev  => '/util',              ensure => 'directory' }
  #chroot::do_bind { "$name/scratch":           dev  => '/scratch',           ensure => 'directory' }
  chroot::do_bind { "$name/etc/cvmfs":         dev  => '/etc/cvmfs',         ensure => 'directory' }

  # Create directories
  file { [ "$name/opt",
           "$name/opt/osg",
           "$name/opt/osg/app",
           "$name/opt/osg/data",
           "$name/mnt/hadoop", ]:
    ensure => 'directory',
    selinux_ignore_defaults => true,
  }

  mount { "$name/opt/osg/data":
    device  => 'hcc-gridnfs:/export/osg/data',
    fstype  => 'nfs',
    ensure  => absent,
    options => 'nfsvers=3,rw,noatime,hard,intr,rsize=32768,wsize=32768',
    atboot  => true,
    require => File["$name/opt/osg/data"],
  }
  mount { "$name/opt/osg/app":
    device  => 'hcc-gridnfs:/export/osg/app',
    fstype  => 'nfs',
    ensure  => absent,
    options => 'nfsvers=3,rw,noatime,hard,intr,rsize=32768,wsize=32768',
    atboot  => true,
    require => File["$name/opt/osg/app"],
  }
  mount { "$name/home":
    device  => 't3-nfs:/export/home',
    fstype  => 'nfs',
    ensure  => mounted,
    options => 'nfsvers=3,rw,noatime,hard,intr,rsize=32768,wsize=32768',
    atboot  => true,
  }
  mount { "$name/mnt/hadoop":
    device   => 'hadoop-fuse-dfs',
    fstype   => 'fuse',
    ensure   => mounted,
    options  => 'server=hadoop-name,port=9000,rdbuffer=32768,allow_other',
    atboot   => true,
    remounts => false,
    require => File["$name/mnt/hadoop"],
  }

  ##################################################
  ##################################################

}

define chroot::do_bind (
  $dev,
  $ensure = '',
) {

  # Bind mount $dev onto $name, creating the file/dir if specified

  if ($ensure) {
    #notify { "Ensuring $dev is $ensure for $name": }
    file { $name:
      ensure => $ensure,
      before => Mount[$name],
      # Don't try to fix things based on matchpathcon
      selinux_ignore_defaults => true,
    }
  }

  mount { $name:
    ensure   => mounted,
    device   => $dev,
    options  => 'bind',
    fstype   => none,
    atboot   => true,
    remounts => true,
  }
}
