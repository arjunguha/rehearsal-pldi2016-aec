class mysql
{
  $packages = [ mysql, mysql-server, "mysql-devel.$architecture" ]

  package { $packages: ensure => installed }

  # CREATE DATABASE abc_userportal;
  # CREATE USER 'abc_userportal'@'localhost' IDENTIFIED BY PASSWORD('abc_userportal');
  # GRANT ALL PRIVILEGES ON abc_userportal.* TO 'abc_userportal'@'localhost' WITH GRANT OPTION;

  #exec { init-postgresql:
  #  user    => "root",
  #  timeout => 600,
  #  command => "/sbin/service postgresql start",
  #  creates => "/var/lib/pgsql/data/pg_hba.conf",
  #  require => Package[postgresql-server];
  #}

  #file { "/etc/sysconfig/pgsql/postgresql":
  #  owner   => "root",
  #  group   => "root",
  #  mode    => 0644,
  #  ensure  => present,
  #  source  => "puppet:///modules/postgres/postgresql.sys",
  #  notify  => Service[postgresql],
  #  require => Exec[init-postgresql];
  #}

  #file { "/var/lib/pgsql/data/postgresql.conf":
  #  owner   => "postgres",
  #  group   => "postgres",
  #  mode    => 0600,
  #  ensure  => present,
  #  source  => "puppet:///modules/postgres/postgresql.conf",
  #  notify  => Service[postgresql],
  #  require => Exec[init-postgresql];
  #}

  firewall::rule { mysql: }

  service { mysqld:
    ensure     => running,
    enable     => true,
    hasstatus  => true,
    hasrestart => true,
    require    => Package[mysql-server];
  }

  nagios::target::service { mysqld: }

  #nagios::service { check_mysql:
  #  args => "mysql!mysql";
  #}
}

define mysql::gem()
{
  exec { "manually install mysql gem":
    path    => "/usr/sbin:/usr/bin/:/sbin:/bin",
    user    => root,
    command => "gem install mysql -- --with-mysql-dir=/usr/mysql --with-mysql-lib=/usr/mysql/lib --with-mysql-include=/usr/mysql/include",
    unless  => "gem list mysql | grep ^mysql",
    require => [ Package[$packages], Package[$devel_pkgs] ];
  }
}

define mysql::database($user, $passwd, $host = "localhost")
{
  exec { "create MySQL user $user":
    path    => "/usr/sbin:/usr/bin/:/sbin:/bin",
    user    => root,
    command => "sleep 30; mysql mysql -e \"CREATE USER $user@$host IDENTIFIED BY '$passwd';\"",
    unless  => "mysql mysql -e \"SELECT user FROM user WHERE user='$user'\" | grep $user",
    require => Service[mysqld];
  }

  exec { "create MySQL database $title":
    path    => "/usr/sbin:/usr/bin/:/sbin:/bin",
    user    => root,
    command => "mysql -e 'CREATE DATABASE $title'",
    unless  => "mysql -e 'SHOW DATABASES' | grep $title",
    require => Exec["create MySQL user $user"];
  }

  exec { "grant MySQL user $user":
    path        => "/usr/sbin:/usr/bin/:/sbin:/bin",
    user        => root,
    command     => "mysql -e \"GRANT ALL PRIVILEGES ON $title.* TO $user@$host IDENTIFIED BY '$passwd'\"",
    refreshonly => true,
    subscribe   => Exec["create MySQL database $title"],
    require     => Exec["create MySQL database $title"];
  }
}
