# Class: kbp_rsync
#
# Action:
#  Installing rsync.
#
# Depends:
#  gen_base
#
class kbp_rsync {
  include gen_base::rsync
}

# Class: kbp_rsync::server_setup
#
# Action:
#  Setup a separate user for rsync on the server, to increase security.
#
# Depends:
#  kbp_rsync
#
class kbp_rsync::server_setup {
  kbp_user { "rsyncuser":
    uid     => 200,
    gid     => 200,
    comment => "Rsync user",
  }

  group { "rsyncuser":
    gid => 200,
  }

  kbp_sudo::rule { "Allow rsyncuser to run rsync as root":
    entity            => 'rsyncuser',
    command           => '/usr/bin/rsync *',
    as_user           => 'root',
    password_required => false,
  }
}

# Define: kbp_rsync::server
#
# Action:
#   Setup acces for cliens to sync from this server.
#
# Parameters:
#   name: The name of the sync, should be the same as the kbp_rsync::client resource that comes with this.
#
# Depends:
#  kbp_rsync
#
define kbp_rsync::server {
  Kbp_rsync::Source_setup <<| tag == "${environment}_${custenv}_rsync_${name}" |>>
}

# Define: kbp_rsync::source_setup
#
# Action:
#  Setup an rsync source location. Always uses root.
#
# Parameters:
#  name:   Used for filename and rsyncd section
#  source: The IP of the source machine
#  key:    The key to use for this resource
#  path:   The path to serve for this location
#
# Depends:
#  kbp_rsync
#
define kbp_rsync::source_setup ($source, $key, $path) {
  include kbp_rsync
  include kbp_rsync::server_setup

  file { "/home/rsyncuser/${name}.conf":
    content => template('kbp_rsync/rsyncd.conf'),
  }

  ssh_authorized_key { "Rsync_for_${name}":
    type    => "ssh-rsa",
    user    => "rsyncuser",
    options => ["from=\"${source}\"","command=\"/usr/bin/sudo /usr/bin/rsync --config=/home/rsyncuser/${name}.conf --server --daemon .\""],
    key     => $key,
  }
}

# Define: kbp_rsync::client
#
# Action:
#  Setup a client for an rsync job. This should be done on the machine which receives the sync, as in, the target.
#
# Parameters:
#  source_host: The host that the data should be pulled from.
#  target_dir:  The target directory on the local machine to which the data should be synced.
#  source_dir:  The source directory on the source host from which to sync the data to the target dir on the local machine.
#  private_key: The private key of the SSH keypair to use for this. This should be generated and pasted in here, to allow us to setup the connection securely.
#               I don't really see a nicer way of doing this.
#  public_key:  The public key generated from the private key above. Used to setup the connection on the source host.
#  hour:        The cron hour parameter for the cronjob that actually performs the sync. Defaults to *, meaning every hour.
#  minute:      The cron minute parameter for the cronjob that actually performs the sync. Defaults to */5, meaning every 5 minutes.
#  bwlimit:     If you'd like to limit the bandwidth used for this sync, you can use this. The number is is kbit/s (as opposed to the rsync bwlimit, which
#               requires a totally inconvenient KBytes/s).
#  target_ip:   The IP address of the target machine, this machine. Defaults to the external ip address as found by the fact.
#  exclude:     The exclude statement for the rsync job. Defaults to false, which disables this feature.
#  chown:       The argument given to 'chown -R' for this directory. Defaults to false, which disables this feature.
#  rsync_tag:   Override the tag for this. Defaults to false, which sets the default tag.
#
# Example:
#  This is an example on how to generate the ssh key:
#
#   $ ssh-keygen -b 2048 -t rsa -N '' -f outkey
#
#  Private key is in the file 'outkey', public key is in the file 'outkey.pub'.
#
# Depends:
#  kbp_rsync
#  kcron
#
define kbp_rsync::client ($source_host, $target_dir, $source_dir, $private_key, $public_key, $hour="*", $minute="*/5", $bwlimit=false, $target_ip=$::external_ipaddress, $include=false, $exclude=false, $chown=false, $rsync_tag=false) {
  # We prefer entering the bwlimit in kbit/s, so we need to convert it to
  # KBytes/s
  if $bwlimit {
    $tmp_bwlimit = $bwlimit / 8
    $real_bwlimit = "--bwlimit ${tmp_bwlimit}"
  } else {
    # Just don't set the option
    $real_bwlimit = ""
  }

  # Custom include parameters
  if $include {
    $real_include = "--include='${include}'"
  } else {
    $real_include = ""
  }

  # Custom exclude parameters
  if $exclude {
    if is_array($exclude) {
      $tmp_exclude = join($exclude, "' --exclude='")
      $real_exclude = "--exclude='${tmp_exclude}'"
    } else {
      $real_exclude = "--exclude='${exclude}'"
    }
  } else {
    $real_exclude = ""
  }

  # Custom chown after the sync
  if $chown {
    $real_chown = "; /bin/chown -R ${chown} ${target_dir}"
  } else {
    $real_chown = ""
  }

  # Setup the secret key
  file {
    "/root/.ssh/rsync-key-${name}":
      mode    => 600,
      content => $private_key;
  }

  # The cronjob that does the actual sync
  kcron { "rsync-${name}":
    command  => "/usr/bin/rsync -qazHSx --delete ${real_bwlimit} ${real_exclude} ${real_include} -e 'ssh -l rsyncuser -i /root/.ssh/rsync-key-${name}' ${source_host}::${name}/* ${target_dir} ${real_chown}",
    user     => "root",
    lockfile => $name,
    hour     => $hour,
    minute   => $minute,
  }

  # Export the setup
  @@kbp_rsync::source_setup { $name:
    source => $target_ip,
    key    => $public_key,
    path   => $source_dir,
    tag    => $rsync_tag ? {
      false   => "${environment}_${custenv}_rsync_${name}",
      default => $rsync_tag,
    },
  }
}
