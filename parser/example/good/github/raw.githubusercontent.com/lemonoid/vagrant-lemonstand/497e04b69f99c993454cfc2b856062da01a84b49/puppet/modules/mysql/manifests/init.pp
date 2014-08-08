class mysql 
{
  package { "mysql-server":
    ensure  => present,
    require => Exec['apt-get update']
  }

  service { "mysql":
    enable => true,
    ensure => running,
    require => Package["mysql-server"],
  }

  exec { "set-mysql-password":
    unless => "/usr/bin/mysqladmin -u${params::mysql_user} -p${params::mysql_password} status",
    command => "/usr/bin/mysqladmin -u${params::mysql_user} password ${params::mysql_password}",
    require => Service["mysql"],
  }

  exec { "create-default-db":
    unless => "/usr/bin/mysql -u${params::mysql_user} -p${params::mysql_password} database",
    command => "/usr/bin/mysql -u${params::mysql_user} -p${params::mysql_password} -e 'create database `${params::mysql_database}`;'",
    require => [Service["mysql"], Exec["set-mysql-password"]]
  }

  exec { "grant-default-db":
    command => "/usr/bin/mysql -u${params::mysql_user} -p${params::mysql_password} -e 'grant all on `${params::mysql_database}`.* to `${params::mysql_user}@localhost`;'",
    require => [Service["mysql"], Exec["create-default-db"]]
  }
}
