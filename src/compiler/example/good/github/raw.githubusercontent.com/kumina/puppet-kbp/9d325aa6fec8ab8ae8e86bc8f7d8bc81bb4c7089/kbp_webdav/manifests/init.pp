# Author: Kumina bv <support@kumina.nl>

# Class: kbp_webdav
#
# Actions:
#  Setup webdav
#
class kbp_webdav {
  include gen_davfs
}

# Define: kbp_webdav::mount
#
# Actions:
#  Setup webdav
#
# Parameters:
#  name: Directory to use as mountpoint. Will be created if not there.
#  webdav_source: Source to mount at mountpoint.
#  dir_mode: Permissons to use for the directory. Defaults to 775.
#
define kbp_webdav::mount ($webdav_source, $dir_mode=775) {
  include kbp_webdav

  file { $name:
    ensure => directory,
    mode   => $dir_mode;
  }

  mount { $name:
    ensure   => mounted,
    device   => $webdav_source,
    options  => 'rw',
    fstype   => 'davfs',
    remounts => false,
    require  => File['/etc/davfs2/davfs2.conf'];
  }

}

