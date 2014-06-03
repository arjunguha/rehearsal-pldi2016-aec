/*

==Class: mysql::server

*/
class mysql::server(
  $logfile_group = undef,
) {

  class { 'mysql::server::base':
    logfile_group => $logfile_group,
  }

  include mysql::config::performance
  include mysql::config::mysqld
  include mysql::config::replication
  include mysql::config::mysqld_safe
  include mysql::config::client
}
