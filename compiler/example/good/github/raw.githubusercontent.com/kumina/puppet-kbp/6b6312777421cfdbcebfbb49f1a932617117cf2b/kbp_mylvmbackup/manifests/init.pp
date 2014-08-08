# Author: Kumina bv <support@kumina.nl>

# Class: kbp_mylvmbackup
#
# Actions:
#  Setup mylvmbackup with the correct config template.
#
# Depends:
#  gen_mylvmbackup
#
class kbp_mylvmbackup {
  include gen_mylvmbackup

  # Pin mylvmbackup to the version from our repo for now
  gen_apt::preference { 'mylvmbackup':
    repo => 'wheezy-kumina';
  }

  File <| title == '/etc/backup/prepare.d/mysql' |> {
    ensure => absent,
  }

  File <| title == '/etc/backup/prepare.d/percona' |> {
    ensure => absent,
  }

  if ! defined(Class['Kbp_backup::Disable']) {
    file { '/etc/backup/prepare.d/mylvmbackup':
      content => template('kbp_mylvmbackup/backup-script.sh'),
      mode    => 755;
    }
  }
}

# Define: kbp_mylvmbackup::config
#
# Actions: Create a config file for mylvmbackup.
#
# Parameters:
#  name: The location of the config file. Should probably be /etc/mylvmbackup.conf, but can be something different.
#  vgname: The name of the Volume Group in which the snapshot is to be created. Needs to be the same as the Volume Group where the MySQL data resides. Defaults to
#          'vg', since that's what we use most.
#  lvname: Name of the Logical Volume to snapshot. Defaults to 'srv', since that's what we use the most.
#  lvsize: Size of the snapshot. Needs to be large enough to accomodate the changes during the backup. Defaults to 1G.
#  relpath: The relative path *on the LV* where to search for the MySQL directory. So for example, if the MySQL data resides in /srv/mysql, but the /srv is a mount of
#           the LV, the relpath option should be set to '/mysql' (the default), since it's in the root of the LV directly. Defaults to '/mysql'.
#
define kbp_mylvmbackup::config ($vgname='vg', $lvname='srv', $lvsize='1G', $relpath='/mysql') {
  include kbp_mylvmbackup

  file { $name:
    content => template('kbp_mylvmbackup/mylvmbackup.conf'),
    require => Package['mylvmbackup'];
  }
}
