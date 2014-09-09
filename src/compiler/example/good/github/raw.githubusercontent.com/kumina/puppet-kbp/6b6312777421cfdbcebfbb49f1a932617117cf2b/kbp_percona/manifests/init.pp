# Author: Kumina bv <support@kumina.nl>

# Parameters:
#  percona_name         The name of this Percona setup, used in combination with $environment to make sure the correct resources are imported
#  slow_query_time    See kbp_percona::server
#
class kbp_percona::mastermaster($percona_tag=false, $serverid, $repl_password, $repl_user='repl', $bind_address="0.0.0.0", $setup_backup=true, $monitoring_ha_slaving=false, $repl_host=$source_ipaddress, $datadir=false, $slow_query_time=10,$serverid, $auto_increment_increment=10, $auto_increment_offset=$serverid, $setup_binlogs=true) {
  if ! $serverid {
    $real_serverid = fqdn_rand(4294967293)+2 # 32 bit integer that is not 0 or 1
  } else {
    $real_serverid = $serverid
  }

  class {
    "kbp_percona::master":
      percona_tag     => $percona_tag,
      bind_address    => $bind_address,
      setup_backup    => $setup_backup,
      serverid        => $real_serverid,
      setup_binlogs   => $setup_binlogs,
      datadir         => $datadir,
      slow_query_time => $slow_query_time;
    "kbp_percona::slave":
      repl_host       => $repl_host,
      percona_tag     => $percona_tag,
      mastermaster    => true,
      monitoring_ha   => $monitoring_ha_slaving,
      datadir         => $datadir,
      slow_query_time => $slow_query_time,
      repl_user       => $repl_user,
      repl_password   => $repl_password;
  }

  file { '/etc/mysql/conf.d/auto_increment.cnf':
    content => "[mysqld]\nauto_increment_increment = ${auto_increment_increment}\nauto_increment_offset = ${auto_increment_offset}",
    require => File['/etc/mysql/conf.d/master.cnf'],
    notify  => Exec['reload-percona'];
  }
}

# Parameters:
#  percona_name       The name of this Percona setup, used in combination with $environment to make sure the correct resources are imported
#  slow_query_time    See kbp_percona::server
#
class kbp_percona::master($percona_tag=false, $bind_address="0.0.0.0", $setup_backup=true, $datadir=false, $serverid=1, $setup_binlogs=true, $slow_query_time=10, $percona_version=false) {
  $real_tag = $percona_tag ? {
    false   => "mysql_${environment}_${custenv}",
    default => "mysql_${environment}_${custenv}_${percona_tag}",
  }

  class { "kbp_percona::server":
    percona_tag     => $percona_tag,
    percona_version => $percona_version,
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

  Gen_percona::Server::Grant <<| tag == $real_tag |>>
  Kbp_percona::Monitoring_dependency <<| tag == $real_tag |>>

  if ! defined(Kbp_percona::Monitoring_dependency["percona_${environment}_${percona_tag}_${fqdn}"]) {
    @@kbp_percona::monitoring_dependency { "percona_${environment}_${percona_tag}_${fqdn}":
      percona_tag => $percona_tag;
    }
  }
}

# Class: kbp_percona::slave
#
# Parameters:
#  percona_name         The name of this Percona setup, used in combination with $environment to make sure the correct resources are imported
#  slow_query_time    See kbp_percona::server
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_percona::slave($percona_tag=false, $bind_address="0.0.0.0", $mastermaster=false, $setup_backup=true, $monitoring_ha=false, $repl_host=$source_ipaddress, $datadir=false, $repl_user='repl', $repl_password,
    $repl_require_ssl=false, $slow_query_time=10) {
  if ! $mastermaster {
    class { "kbp_percona::server":
      percona_tag     => $percona_tag,
      setup_backup    => $setup_backup,
      bind_address    => $bind_address,
      datadir         => $datadir,
      slow_query_time => $slow_query_time;
    }
  }

  $real_tag = $percona_tag ? {
    false   => "mysql_${environment}_${custenv}",
    default => "mysql_${environment}_${custenv}_${percona_tag}",
  }

  @@gen_percona::server::grant { "repl_${fqdn}":
    user        => $repl_user,
    password    => $repl_password,
    hostname    => $repl_host,
    db          => '*',
    permissions => "replication slave",
    require_ssl => $repl_require_ssl,
    tag         => $real_tag;
  }

  kbp_ferm::rule { "Percona slaving":
    exported => true,
    saddr    => $repl_host,
    proto    => "tcp",
    dport    => 3306,
    action   => "ACCEPT",
    ferm_tag => $real_tag;
  }

  kbp_icinga::service { "percona_slaving":
    service_description => "Percona slaving",
    check_command       => "check_mysql_slave",
    nrpe                => true,
    ha                  => $monitoring_ha,
    check_interval      => 60;
  }

  kbp_icinga::servicedependency { "percona_dependency_slaving_service":
    dependent_service_description => "Percona slaving",
    service_description           => "Percona service",
    execution_failure_criteria    => "u,w,c",
    notification_failure_criteria => "u,w,c";
  }
}

# Class: kbp_percona::server
#
# Parameters:
#  percona_name       The name of this Percona setup, used in combination with $environment to make sure the correct resources are imported
#  slow_query_time  Slow query log time in seconds; see percona documentation for long_query_time global variable. Set to false or 0 to disable.
#
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_percona::server($percona_tag=false, $percona_version=false, $bind_address="0.0.0.0", $setup_backup=true, $datadir=false, $charset=false, $slow_query_time=10) {
  include kbp_trending::mysql
  include kbp_percona::monitoring::icinga::server
  class { "gen_percona::server":
    version => $percona_version,
    datadir => $datadir;
  }

  $real_tag = $percona_tag ? {
    false   => "mysql_${environment}_${custenv}",
    default => "mysql_${environment}_${custenv}_${percona_tag}",
  }

  class { 'kbp_collectd::plugin::mysql':
    mysql_tag => $percona_tag;
  }

  if $setup_backup and ! defined(Class['Kbp_backup::Disable']) {
    file { "/etc/backup/prepare.d/percona":
      ensure  => link,
      target  => "/usr/share/backup-scripts/prepare/mysql",
      require => Package["backup-scripts"];
    }

    # Since we often update a MySQL to Percona, make sure we remove the old cronjob
    file { '/etc/backup/prepare.d/mysql':
      ensure => absent;
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
    # Remove the backup script. Don't remove the expire_logs, since that might inadvertently fill up a disk
    # where binlogs are created but no longer removed. We just remove them earlier.
    file { "/etc/backup/prepare.d/percona":
      ensure => absent,
    }
  }

  file {
    "/etc/mysql/conf.d/bind-address.cnf":
      content => "[mysqld]\nbind-address = ${bind_address}\n",
      notify  => Service["percona"];
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
        require => Package[$gen_percona::server::perconaserver];
      }
    }
  }

  # Since we usually upgrade to Percona, remove the old logrotate config for mysql
  file { '/etc/logrotate.d/mysql-server':
    ensure => absent,
  }

  exec { 'remove_root_users':
    onlyif  => '/usr/bin/mysql --defaults-file=/etc/mysql/debian.cnf -e "select * from mysql.user where user=\'root\' and password=\'\'" | /bin/grep -q root',
    command => '/usr/bin/mysql --defaults-file=/etc/mysql/debian.cnf -e "delete from mysql.user where user=\'root\'; flush privileges"',
    require => Service["percona"];
  }

  Mysql::Server::Grant <<| tag == $real_tag |>>
  Kbp_ferm::Rule <<| tag == $real_tag |>>
  Gen_ferm::Rule <<| tag == "percona_monitoring" |>>

  # Stay compatible with MySQL
  Gen_ferm::Rule <<| tag == "mysql_monitoring" |>>
}

# Class: kbp_percona::server::ssl
#
# Parameters:
#  certname
#    The filename (without extention) of the keyfile and certificate (installed using kbp_ssl::keys{}).
#  intermediate
#    The name of the intermediate certificate in use.
#
# Actions:
#  Activate the ability to connect over SSL to the Percona server
#
# Depends:
#  kbp_percona::server
#  kbp_ssl::keys
#  gen_puppet
#
class kbp_percona::server::ssl ($certlocation="database/ssl/${name}", $intermediate){
  class { 'kbp_mysql::server::ssl':
    certlocation => $certlocation,
    intermediate => $intermediate,
  }

  Kbp_ssl::Keys <| title == $certlocation |> {
    require => Package['percona-server'],
  }
}

# Class: kbp_percona::monitoring::icinga::server
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
class kbp_percona::monitoring::icinga::server($otherhost=false) {
  kbp_icinga::service {
    "percona":
      service_description => "Percona service",
      check_command       => "check_mysql",
      nrpe                => true;
    "percona_connlimit":
      service_description => "Percona service connection limit",
      check_command       => "check_mysql_connlimit",
      nrpe                => true;
  }

  kbp_icinga::servicedependency { "percona_dependency_connlimit_service":
    dependent_service_description => "Percona service connection limit",
    service_description           => "Percona service",
    execution_failure_criteria    => "u,w,c",
    notification_failure_criteria => "u,w,c";
  }

  Gen_ferm::Rule <<| tag == 'mysql_monitoring' |>>

  Mysql::Server::Grant <<| tag == 'mysql_monitoring' |>>

  File <<| tag == 'mysql_monitoring' |>>
}

class kbp_percona::client::java {
  include percona::java
  fail("This class is untested and simply a copy from kbp_mysql.")
}

# Define: kbp_percona::client
#
# Parameters:
#  percona_name
#    The name of the service that's using Percona
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
define kbp_percona::client ($percona_tag=false, $address=$source_ipaddress, $environment=$environment) {
  include gen_base::mysql_client

  $real_tag = $percona_tag ? {
    false   => "mysql_${environment}_${custenv}",
    default => "mysql_${environment}_${custenv}_${percona_tag}",
  }

  kbp_ferm::rule { "Percona connections for ${name}":
    exported => true,
    saddr    => $address,
    proto    => "tcp",
    dport    => 3306,
    action   => "ACCEPT",
    ferm_tag => $real_tag;
  }
}

define kbp_percona::monitoring_dependency($this_fqdn=$fqdn, $percona_tag=false) {
  if $this_fqdn != $fqdn {
    $real_tag = $percona_tag ? {
      false   => "mysql_${environment}_${custenv}",
      default => "mysql_${environment}_${custenv}_${percona_tag}",
    }

    gen_icinga::servicedependency { "percona_dependency_${fqdn}":
      dependent_service_description => "Percona service",
      host_name                     => $this_fqdn,
      service_description           => "Percona service",
      tag                           => $real_tag;
    }
  }
  fail("This define is untested and simply a copy from kbp_mysql.")
}
