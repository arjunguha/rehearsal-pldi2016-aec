# Author: Kumina bv <support@kumina.nl>

# Define: kbp_drbd
#
# Parameters:
#  otherhost
#    Undocumented
#  mount_options
#    Set specific mount options for the actual mount point. Defaults to nodev,nosuid,noatime,acl,nointr.
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
define kbp_drbd($standalone=false, $drbd_tag=false, $mastermaster=true, $time_out=false, $connect_int=false, $ping_int=false, $ping_timeout=false, $after_sb_0pri='discard-younger-primary', $after_sb_1pri='discard-secondary',
    $after_sb_2pri='call-pri-lost-after-sb', $rate='5M', $verify_alg='md5', $use_ipaddress=$external_ipaddress, $mount_options='nodev,nosuid,noatime,acl,nointr', $disk_flushes=true, $max_buffers=false,
    $unplug_watermark=false, $sndbuf_size=false, $al_extents=false, $disk) {
  include kbp_trending::drbd
  include kbp_collectd::plugin::drbd

  $real_tag = $drbd_tag ? {
    false   => "drbd_${environment}_${custenv}",
    default => "drbd_${environment}_${custenv}_${drbd_tag}",
  }

  if $mastermaster {
    class { 'kbp_ocfs2':
      use_ipaddress => $use_ipaddress,
      ocfs2_tag     => $drbd_tag;
    }

    mount { $name:
      ensure   => mounted,
      device   => '/dev/drbd1',
      fstype   => 'ocfs2',
      options  => $mount_options,
      dump     => 0,
      pass     => 0,
      remounts => true,
      target   => '/etc/fstab',
      require  => Gen_drbd[$name];
    }

    file {
      "${name}/.monitoring":
        content => "DRBD_mount_ok",
        require => Mount[$name];
      "/etc/insserv/overrides/ocfs2":
        notify  => Exec["reload insserv for ocfs2"],
        content => template('kbp_drbd/ocfs2.init.override');
    }

    exec { "reload insserv for ocfs2":
      command     => "/sbin/insserv -r ocfs2; /sbin/insserv ocfs2",
      refreshonly => true;
    }

    kbp_icinga::drbd { $name:
      standalone => $standalone;
    }
  }

  gen_drbd { $name:
    use_ipaddress    => $use_ipaddress,
    mastermaster     => $mastermaster,
    time_out         => $time_out,
    connect_int      => $connect_int,
    ping_int         => $ping_int,
    ping_timeout     => $ping_timeout,
    after_sb_0pri    => $after_sb_0pri,
    after_sb_1pri    => $after_sb_1pri,
    after_sb_2pri    => $after_sb_2pri,
    disk_flushes     => $disk_flushes,
    max_buffers      => $max_buffers,
    unplug_watermark => $unplug_watermark,
    sndbuf_size      => $sndbuf_size,
    al_extents       => $al_extents,
    rate             => $rate,
    verify_alg       => $verify_alg,
    drbd_tag         => $real_tag,
    disk             => $disk;
  }

  Kbp_ferm::Rule <<| tag == $real_tag |>>

  kbp_ferm::rule { "DRBD connections for ${name}":
    saddr    => $use_ipaddress,
    proto    => 'tcp',
    dport    => 7789,
    action   => 'ACCEPT',
    exported => true,
    ferm_tag => $real_tag;
  }
}
