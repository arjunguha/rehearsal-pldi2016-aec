# Author: Kumina bv <support@kumina.nl>

# Parameters:
#  mysql_tag
#    The name of this MySQL setup, used in combination with $environment to make sure the correct resources are imported
class kbp_mysql::mastermaster($mysql_tag=false, $serverid=false, $auto_increment_increment=10, $auto_increment_offset=$serverid, $setup_binlogs=true, $bind_address="0.0.0.0", $setup_backup=true,
    $monitoring_ha_slaving=false, $repl_host=$source_ipaddress, $datadir=false, $slow_query_time=10, $repl_password, $repl_user='repl') {
  if ! $serverid {
    $real_serverid = fqdn_rand(4294967293)+2 # 32 bit integer that is not 0 or 1
  } else {
    $real_serverid = $serverid
  }

  class {
    "kbp_mysql::master":
      mysql_tag       => $mysql_tag,
      bind_address    => $bind_address,
      setup_backup    => $setup_backup,
      serverid        => $real_serverid,
      setup_binlogs   => $setup_binlogs,
      datadir         => $datadir,
      slow_query_time => $slow_query_time;
    "kbp_mysql::slave":
      repl_host       => $repl_host,
      mysql_tag       => $mysql_tag,
      mastermaster    => true,
      monitoring_ha   => $monitoring_ha_slaving,
      datadir         => $datadir,
      slow_query_time => $slow_query_time,
      repl_user       => $repl_user,
      repl_password   => $repl_password;
  }

  if $real_serverid != $auto_increment_offset {
    $real_auto_increment_offset = regsubst($hostname,'[^0-9]*(\d)','\1')
  } else {
    $real_auto_increment_offset = $real_serverid
  }

  if $real_auto_increment_offset !~ /^\d$/ {
    fail("Unable to distill an auto-increment-offset setting from the hostname ${hostname}, please supply it")
  }

  file { '/etc/mysql/conf.d/auto_increment.cnf':
    content => "[mysqld]\nauto_increment_increment = ${auto_increment_increment}\nauto_increment_offset = ${real_auto_increment_offset}",
    require => File['/etc/mysql/conf.d/master.cnf'],
    notify  => Exec['reload-mysql'];
  }
}

# Parameters:
#  mysql_tag
#    The name of this MySQL setup, used in combination with $environment to make sure the correct resources are imported
#  bind_address:
#    The address to bind the server to
#  setup_backup:
#    Backup this mysql server
#  datadir:
#    Root directory for all the mysql data.
#  slow_query_time    See kbp_mysql::server
class kbp_mysql::master($mysql_tag=false, $bind_address="0.0.0.0", $setup_backup=true, $datadir=false, $serverid=1, $setup_binlogs = true, $slow_query_time=10) {
  $real_tag = $mysql_tag ? {
    false   => "mysql_${environment}_${custenv}",
    default => "mysql_${environment}_${custenv}_${mysql_tag}",
  }

  class { "kbp_mysql::server":
    mysql_tag       => $mysql_tag,
    setup_backup    => $setup_backup,
    bind_address    => $bind_address,
    datadir         => $datadir,
    slow_query_time => $slow_query_time;
  }

  file { '/etc/mysql/conf.d/master.cnf':
    content => template('kbp_mysql/master.cnf'),
    require => Service['mysql'],
    notify  => Exec['reload-mysql'];
  }

  if ! defined(Kbp_mysql::Monitoring_dependency["mysql_${environment}_${mysql_tag}_${fqdn}"]) {
    @@kbp_mysql::monitoring_dependency { "mysql_${environment}_${mysql_tag}_${fqdn}":
      mysql_tag => $mysql_tag;
    }
  }
}

# Class: kbp_mysql::slave
#
# Parameters:
#  mysql_tag         The name of this MySQL setup, used in combination with $environment to make sure the correct resources are imported
#  slow_query_time    See kbp_mysql::server
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_mysql::slave($mysql_tag=false, $bind_address="0.0.0.0", $mastermaster=false, $setup_backup=true, $monitoring_ha=false, $repl_host=$source_ipaddress, $datadir=false, $repl_user='repl', $repl_password, $repl_require_ssl=false,
    $serverid=false, $slow_query_time=10) {
  $real_tag = $mysql_tag ? {
    false   => "mysql_${environment}_${custenv}",
    default => "mysql_${environment}_${custenv}_${mysql_tag}",
  }

  if ! $mastermaster {
    class { "kbp_mysql::server":
      mysql_tag       => $mysql_tag,
      setup_backup    => $setup_backup,
      bind_address    => $bind_address,
      datadir         => $datadir,
      slow_query_time => $slow_query_time;
    }

    file { '/etc/mysql/conf.d/master.cnf':
      ensure => absent;
    }

    if ! $serverid {
      $real_serverid = fqdn_rand(4294967293)+2 # 32 bit number that cannot be 0 or 1 (1=master usually)
    } else {
      $real_serverid = $serverid
    }

    file { '/etc/mysql/conf.d/slave.cnf':
      content => "[mysqld]\nserver-id = ${real_serverid}",
      require => Service['mysql'],
      notify  => Exec['reload-mysql'];
    }
  }

  @@mysql::server::grant { "repl_${fqdn}":
    user        => $repl_user,
    password    => $repl_password,
    hostname    => $repl_host,
    db          => '*',
    permissions => "replication slave",
    require_ssl => $repl_require_ssl,
    tag         => $real_tag;
  }

  kbp_ferm::rule { "MySQL slaving":
    exported => true,
    saddr    => $repl_host,
    proto    => "tcp",
    dport    => 3306,
    action   => "ACCEPT",
    ferm_tag => $real_tag;
  }

  kbp_icinga::service { "mysql_slaving":
    service_description => "MySQL slaving",
    check_command       => "check_mysql_slave",
    nrpe                => true,
    ha                  => $monitoring_ha,
    check_interval      => 60;
  }

  kbp_icinga::servicedependency { "mysql_dependency_slaving_service":
    dependent_service_description => "MySQL slaving",
    service_description           => "MySQL service",
    execution_failure_criteria    => "u,w,c",
    notification_failure_criteria => "u,w,c";
  }
}

# Class: kbp_mysql::server
#
# Parameters:
#  mysql_tag       The name of this MySQL setup, used in combination with $environment to make sure the correct resources are imported
#  slow_query_time  Slow query log time in seconds; see mysql documentation for long_query_time global variable. Set to false or 0 to disable.
#
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_mysql::server($mysql_tag=false, $bind_address="0.0.0.0", $setup_backup=true, $datadir=false, $charset=false, $slow_query_time=10) {
  include kbp_trending::mysql
  include kbp_mysql::monitoring::icinga::server
  class { "mysql::server":
    datadir => $datadir;
  }

  if ! $datadir {
    notify { 'This server is not using /srv/mysql as MySQL datadir. Please provide the correct datadir in the puppet code!':; }
  }

  $real_tag = $mysql_tag ? {
    false   => "mysql_${environment}_${custenv}",
    default => "mysql_${environment}_${custenv}_${mysql_tag}",
  }
  class { 'kbp_collectd::plugin::mysql':
    mysql_tag => $mysql_tag;
  }

  if $setup_backup and ! defined(Class['Kbp_backup::Disable']) {
    file { "/etc/backup/prepare.d/mysql":
      ensure  => link,
      target  => "/usr/share/backup-scripts/prepare/mysql",
      require => Package["backup-scripts"];
    }

    if $datadir {
      if ! defined(Kbp_backup::Exclude[$datadir]) {
        kbp_backup::exclude { $datadir:; }
      }
    } else {
      if ! defined(Kbp_backup::Exclude['/var/lib/mysql/']) {
        kbp_backup::exclude { '/var/lib/mysql/':; }
      }
    }
  } else {
    file { "/etc/backup/prepare.d/mysql":
      ensure => absent;
    }
  }

  file {
    "/etc/mysql/conf.d/bind-address.cnf":
      content => "[mysqld]\nbind-address = ${bind_address}\n",
      notify  => Service["mysql"];
    "/etc/mysql/conf.d/character-set-server.cnf":
      ensure  => absent;
#      content => "[mysqld]\ncharacter-set-server = 'utf8'\n",
#      notify  => Service["mysql"];
    "/etc/mysql/conf.d/expire_logs.cnf":
      content => "[mysqld]\nexpire_logs_days = 1\n";
  }

  case $slow_query_time {
    false, 'false', 0, '0', /0\.0+$/: {
      file { '/etc/mysql/conf.d/slow-query-log.cnf':
        ensure => absent;
      }
    }
    default: {
      file { '/etc/mysql/conf.d/slow-query-log.cnf':
        content => template('kbp_mysql/slow-query-log.cnf'),
        require => Package[$mysql::server::mysqlserver];
      }
    }
  }

  exec { 'remove_root_users':
    onlyif  => '/usr/bin/mysql --defaults-file=/etc/mysql/debian.cnf -e "select * from mysql.user where user=\'root\' and password=\'\'" | /bin/grep -q root',
    command => '/usr/bin/mysql --defaults-file=/etc/mysql/debian.cnf -e "delete from mysql.user where user=\'root\'; flush privileges"',
    require => Service["mysql"];
  }

  Kbp_ferm::Rule <<| tag == $real_tag |>>

  Mysql::Server::Grant <<| tag == $real_tag |>>
  Kbp_mysql::Monitoring_dependency <<| tag == $real_tag |>>
}

# Class: kbp_mysql::server::ssl
#
# Parameters:
#  certlocation:
#    The location of the keyfile and certificate (used for kbp_ssl::keys{}).
#  intermediate
#    The name of the intermediate certificate in use.
#
# Actions:
#  Activate the ability to connect over SSL to the MySQL server
#
# Depends:
#  kbp_mysql::server
#  kbp_ssl::keys
#  gen_puppet
#
class kbp_mysql::server::ssl ($certlocation="database/ssl/${fqdn}", $intermediate){
  include "kbp_ssl::intermediate::${intermediate}"
  $certname = regsubst($certlocation, '([^\/]*\/)*', '')
  $intermediate_name = template("kbp_ssl/translate_names.erb")

  file { "/etc/mysql/conf.d/ssl.cnf":
    content  => "[mysqld]\nssl\nssl-ca=/etc/ssl/certs/${intermediate_name}.pem\nssl-cert=/etc/ssl/certs/${certname}.pem\nssl-key=/etc/ssl/private/${certname}.key",
    require => File["/etc/ssl/certs/${intermediate_name}.pem", "/etc/ssl/certs/${certname}.pem", "/etc/ssl/private/${certname}.key"],
    notify  => Exec['reload-mysql'];
  }

  setfacl { "Allow MySQL read access to /etc/ssl/private":
    dir     => '/etc/ssl/private',
    recurse => false,
    acl     => 'user:mysql:--x';
  }

  kbp_ssl::keys { $certlocation:
    owner   => 'mysql',
    require => Package['mysql-server'];
  }
}

# Class: kbp_mysql::monitoring::icinga::server
#
# Parameters:
#  otherhost
#    Undocumented
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_mysql::monitoring::icinga::server($otherhost=false) {
  kbp_icinga::service {
    "mysql":
      service_description => "MySQL service",
      check_command       => "check_mysql",
      nrpe                => true;
    "mysql_connlimit":
      service_description => "MySQL service connection limit",
      check_command       => "check_mysql_connlimit",
      nrpe                => true;
    "mysqldump":
      service_description => "MySQLdump status",
      check_command       => "check_mysqldump",
      max_check_attempts  => 8640,
      nrpe                => true,
      sms                 => false,
      customer_notify     => false;
  }

  kbp_icinga::servicedependency { "mysql_dependency_connlimit_service":
    dependent_service_description => "MySQL service connection limit",
    service_description           => "MySQL service",
    execution_failure_criteria    => "u,w,c",
    notification_failure_criteria => "u,w,c";
  }

  Gen_ferm::Rule <<| tag == 'mysql_monitoring' |>>

  Mysql::Server::Grant <<| tag == 'mysql_monitoring' |>>

  File <<| tag == 'mysql_monitoring' |>>
}

class kbp_mysql::client::java {
  include mysql::java
}

# Define: kbp_mysql::client
#
# Parameters:
#  mysql_tag
#    The name of the service that's using MySQL
#
# Actions:
#  Open the firewall on the server to allow access from this client.
#  Make sure the title of the resource is something sane, since if you
#  use "dummy" everywhere, it still clashes.
#
# Depends:
#  kbp_ferm
#  gen_puppet
#
define kbp_mysql::client ($mysql_tag=false, $address=$source_ipaddress, $environment=$environment, $address6=$source_ipaddress6) {
  include gen_base::mysql_client

  $real_tag = $mysql_tag ? {
    false   => "mysql_${environment}_${custenv}",
    default => "mysql_${environment}_${custenv}_${mysql_tag}",
  }

  kbp_ferm::rule { "MySQL connections for ${name}":
    exported => true,
    saddr    => $address,
    proto    => "tcp",
    dport    => 3306,
    action   => "ACCEPT",
    ferm_tag => $real_tag;
  }

  if $address6 {
    kbp_ferm::rule { "MySQL connections for ${name}_v6":
      exported => true,
      saddr    => $address6,
      proto    => "tcp",
      dport    => 3306,
      action   => "ACCEPT",
      ferm_tag => $real_tag;
    }
  }
}

define kbp_mysql::monitoring_dependency($this_fqdn=$fqdn, $mysql_tag=false) {
  if $this_fqdn != $fqdn {
    $real_tag = $mysql_tag ? {
      false   => "mysql_${environment}_${custenv}",
      default => "mysql_${environment}_${custenv}_${mysql_tag}",
    }

    gen_icinga::servicedependency { "mysql_dependency_${fqdn}":
      dependent_service_description => "MySQL service",
      host_name                     => $this_fqdn,
      service_description           => "MySQL service",
      tag                           => $real_tag;
    }
  }
}
