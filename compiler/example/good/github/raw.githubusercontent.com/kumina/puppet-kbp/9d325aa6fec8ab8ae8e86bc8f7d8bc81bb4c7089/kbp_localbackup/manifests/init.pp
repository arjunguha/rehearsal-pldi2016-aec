# Author: Kumina bv <support@kumina.nl>

# Class: kbp_localbackup
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_localbackup {
  package { "rsnapshot":
    ensure => installed,
  }

  file { "/etc/rsnapshot.conf":
    owner => "root",
    group => "root",
    mode => 644,
    content => template("kbp_localbackup/rsnapshot/rsnapshot.conf"),
    require => Package["rsnapshot"],
  }

  file { "/usr/local/bin/rsnapshot_symlinks":
    content => template("kbp_localbackup/rsnapshot_symlinks"),
    owner => "root",
    group => "staff",
    mode => 755,
  }

  file { "/etc/cron.d/rsnapshot":
    content => template("kbp_localbackup/rsnapshot/cron.d/rsnapshot"),
    owner => "root",
    group => "root",
    mode => 644,
    require => File["/etc/rsnapshot.conf"],
  }
}
