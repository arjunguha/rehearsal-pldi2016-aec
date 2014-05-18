# Author: Kumina bv <support@kumina.nl>

# Define: kbp_nfs::client::mount
#
# Parameters:
#  source
#    Undocumented
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
define kbp_nfs::client::mount($server, $mount_options="wsize=1024,rsize=1024,vers=3", $export_options="rw,sync,no_subtree_check", $serverpath=false, $nfs_tag="default", $ferm_saddr=$fqdn, $nfs_client=$fqdn, $enable_cache=false) {
  include kbp_trending::nfs
  include kbp_collectd::plugin::nfs

  $real_serverpath = $serverpath ? {
    false   => $name,
    default => $serverpath,
  }
  $real_tag = "nfs_${environment}_${custenv}_${nfs_tag}"

  # This will probably end up opening the same ports for the same hosts multiple times on the
  # server if you have several mounts, but that's not a problem.
  kbp_ferm::rule { "NFS connections from ${fqdn} for ${real_serverpath}":
    exported => true,
    saddr    => $ferm_saddr,
    proto    => "(tcp udp)",
    action   => "ACCEPT",
    ferm_tag => $real_tag;
  }

  kbp_icinga::nfs::client { $name:; }

  kbp_backup::exclude { "exclude_nfsmount_${name}":
    content => "${name}/*";
  }

  @@kbp_nfs::client::export_opts { "${name} mount options for ${fqdn}":
    location => $real_serverpath,
    options  => $export_options,
    client   => $nfs_client,
    tag      => $real_tag;
  }

  if $enable_cache {
    include gen_nfs::cachefilesd

    if $lsbdistcodename != 'wheezy' {
      fail('We had trouble with unstable nodes on Squeeze, even when using backported kernel and cachefilesd. Better not enable it.')
    }

    gen_nfs::mount { $name:
      source  => "${server}:${real_serverpath}",
      require => Service['cachefilesd'],
      options => "${mount_options},fsc";
    }
  } else {
    gen_nfs::mount { $name:
      source  => "${server}:${real_serverpath}",
      options => $mount_options;
    }
  }
}

define kbp_nfs::client::export_opts($location, $options, $client) {
  if !defined(Concat::Add_content[$location]) {
    concat::add_content {
      $location:
        content => "${location} \\",
        target  => "/etc/exports";
      "${location}_aaaaa":
        content => "",
        target  => "/etc/exports";
    }

    file { "$location/.monitoring":
      content => "NFS_mount_ok\n";
    }
  }

  concat::add_content { "${location}_${client}":
    content => "${client}($options) \\",
    target  => "/etc/exports";
  }
}
