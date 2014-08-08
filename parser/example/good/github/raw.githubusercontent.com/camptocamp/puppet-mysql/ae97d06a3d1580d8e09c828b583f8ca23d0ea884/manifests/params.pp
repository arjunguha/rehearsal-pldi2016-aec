class mysql::params {

  $mycnf = $::osfamily ? {
    'RedHat' => '/etc/my.cnf',
    default  => '/etc/mysql/my.cnf',
  }

  $mycnfctx = "/files${mycnf}"

  $data_dir = $mysql_data_dir ? {
    ''      => '/var/lib/mysql',
    default => $mysql_data_dir,
  }

  $backup_dir = $mysql_backupdir ? {
    ''      => '/var/backups/mysql',
    default => $mysql_backupdir,
  }

  $logfile_group = $mysql_logfile_group ? {
    ''      => $::osfamily ? {
        'RedHat' => 'mysql',
        'Debian' => 'adm',
        default  => 'adm',
      },
    default => $mysql_logfile_group,
  }

}
