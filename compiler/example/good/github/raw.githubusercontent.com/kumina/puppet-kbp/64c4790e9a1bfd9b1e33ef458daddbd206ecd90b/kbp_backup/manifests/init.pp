class kbp_backup::server {
  include offsitebackup::server

  Kbp_icinga::Clientcommand <| title == 'disk_space' |> {
    arguments => "-W 5% -K 2% -w 5% -c 2% -l --errors-only -t 20",
  }
}

class kbp_backup::disable {
  Kbp_backup::Client <| |> {
    ensure => absent,
  }

  Kbp_backup::Exclude <| |> {
    ensure => absent,
  }
}

define kbp_backup::client($ensure="present", $method="offsite", $backup_server="backup2.kumina.nl", $backup_home="/backup/${environment}", $backup_user=$environment, $backup_remove_older_than="30B", $splay=28800, $etc_only=false) {
  $real_method = $ensure ? {
    "absent" => "absent",
    absent   => "absent",
    default  => $method,
  }

  case $real_method {
    "absent": {
      package { ["offsite-backup","localbackup","backup-scripts"]:
        ensure => purged;
      }
    }
    "offsite": {
      $package = "offsite-backup"

      class { "offsitebackup::client":
        splay                    => $splay,
        backup_server            => $backup_server,
        backup_home              => $backup_home,
        backup_user              => $backup_user,
        backup_remove_older_than => $backup_remove_older_than;
      }
    }
    "local":   {
      $package = "local-backup"

      class { "localbackup::client":
        backup_home => $backup_home;
      }
    }
    default:   {
      fail("Invalid method (${method}) for kbp_backup::client")
    }
  }

  if $ensure == "absent" {
    file { "/etc/backup/includes":
      ensure  => $ensure;
    }

    concat { "/etc/backup/excludes":
      ensure  => $ensure;
    }
  } else {
    file { "/etc/backup/includes":
      ensure  => $ensure,
      content => $etc_only ? {
        true    => "/etc/\n",
        default => "/\n",
      },
      require => Package[$package];
    }

    concat { "/etc/backup/excludes":
      ensure  => $ensure,
      require => Package[$package];
    }
    if $lsbdistcodename == 'squeeze' {
      gen_apt::preference { 'rdiff-backup':
        repo => 'squeeze-kumina';
      }
    }
  }

  kbp_backup::exclude { "excludes_base":
    ensure  => $ensure,
    content => template("kbp_backup/excludes_base");
  }

  if $ensure == "present" {
    kbp_icinga::service { "daily_backup":
      service_description => "Daily backup status",
      check_command       => "check_backup",
      nrpe                => true,
      sms                 => false,
      check_interval      => '300',
      customer_notify     => false,
    }

    kbp_icinga::servicedependency { "daily_backup_backup_status":
      service_description           => "Backup status",
      dependent_service_description => "Daily backup status",
      execution_failure_criteria    => "w",
      notification_failure_criteria => "w";
    }

    # If the backupserver is down, we don't need notifications
    # TODO workaround for a backup server that's not present in this puppetmaster
    if $real_method == 'offsite' and defined(Sshkey[$backup_server]) {
      kbp_icinga::servicedependency { "daily_backup_ssh_on_server":
        service_description           => 'SSH connectivity',
        host_name                     => $backup_server,
        dependent_service_description => 'Daily backup status',
        execution_failure_criteria    => 'w,c,u',
        notification_failure_criteria => 'w,c,u';
      }
    }
  }
}

define kbp_backup::exclude($ensure="present", $content=$name) {
  $sanitized_name = regsubst($name, '[^a-zA-Z0-9\-_]', '_', 'G')

  concat::add_content { $sanitized_name:
    ensure  => $ensure,
    content => $content,
    target  => "/etc/backup/excludes";
  }
}
