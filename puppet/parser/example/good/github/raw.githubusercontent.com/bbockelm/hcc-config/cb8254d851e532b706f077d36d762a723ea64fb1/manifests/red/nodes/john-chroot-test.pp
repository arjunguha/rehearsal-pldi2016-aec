node 'red-d18n2' inherits red-private {
  $role = "red-worker-el6"
  $condorCustom09 = "el6"
  $isHDFSDatanode = true
  include general

  chroot::root { 'sl6':
    version => 1,
    yum     => 'puppet:///modules/chroot/yum-sl6.conf',
    rpms      => 'acl attr bind-utils cyrus-sasl-plain lsof libcgroup quota rhel-instnum cpuspeed dos2unix m2crypto sssd nc prctl setarch tree unix2dos unzip wget zip zlib glibc-devel perl-Compress-Zlib',
    rpms_suid => 'osg-wn-client glexec lcmaps-plugins-condor-update lcmaps-plugins-process-tracking lcmaps-plugins-mount-under-scratch',
  }

}

