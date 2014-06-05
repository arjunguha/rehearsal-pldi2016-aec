class backup
{
  $backupuser = $params::mysql_user
  $backuppassword = $params::mysql_password
  $backupdir = $params::mysql_backup_dir

  file { 'mysqlbackup.sh':
    ensure  => present,
    path    => '/usr/local/bin/mysqlbackup.sh',
    mode    => '0700',
    owner   => 'root',
    group   => 'root',
    content => template('backup/mysqlbackup.sh.erb'),
  }

  file { 'mysqlbackupdir':
    ensure => 'directory',
    path   => "${params::mysql_backup_dir}",
    mode   => '0700',
    owner  => 'root',
    group  => 'root',
  }

  cron { 'mysqlbackup':
    ensure  => present,
    command => '/usr/local/bin/mysqlbackup.sh',
    user    => 'root',
    hour    => "*",
    minute  => 0,
    require => [
      File["mysqlbackup.sh"],
      File["mysqlbackupdir"],
    ],
  }
}
