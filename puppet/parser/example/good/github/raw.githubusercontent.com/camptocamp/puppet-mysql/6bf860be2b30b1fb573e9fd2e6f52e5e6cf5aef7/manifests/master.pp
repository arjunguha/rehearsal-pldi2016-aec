class mysql::master inherits mysql::server::base {
  include mysql::config::replication::master
}
