class mysql::client (
  $user     = "root",
  $password = undef,
) {
  include mysql::settings

  # we'll need this regardless, for percona-toolkit
  realize(Yumrepo["percona"])

  $client_package_name = $mysql::settings::package_type ? {
  # mysql56 shows how exact package #'s, you may not want that
    "mysql56"   => ["MySQL-client-5.6.12", "MySQL-shared-compat-5.6.12", "MySQL-shared-5.6.12"],
    "percona55" => ["Percona-Server-client-55", "Percona-Server-shared-compat"],
    "mariadb55" => ["MariaDB-client","MariaDB-compat","MariaDB-common"],
    "percona51" => ["Percona-Server-client-51"],
    default     => "mysql",
  }


  if $package_type == 'mysql56' {
    yumrepo { 'mariadb':
      ensure => absent
    }
    # realize(Yumrepo['your-mysql56-repo'])
  }

  if $package_type == "mariadb55" {
      realize(Yumrepo["mariadb55"])
  }

  package { $client_package_name:
    ensure          => present,
    require         => $package_type ? {
      # "mysql56"   => Yumrepo["your-mysql56-repo"],
      "percona55" => Yumrepo["percona"],
      "mariadb55" => Yumrepo["mariadb55"],
      "tokutek"   => undef,
      "percona51" => Yumrepo["percona"],
      default     => undef,
     }
  }

  if $password != undef {
    file { '/root/.my.cnf':
    ensure => file,
    mode => '0600',
    owner => "root",
    group => "root",
    replace => false,
    content => template("mysql/dot-my.cnf.erb"),
    require => Package[$client_package_name];
    }
  }

  package { 'percona-toolkit':
    ensure => present,
    require => Package[$client_package_name];
    'percona-xtrabackup':
       ensure => present;
    'mysql-utilities':
       ensure => present;
    'perl-DBD-MySQL':
       ensure => present;
  }
}
