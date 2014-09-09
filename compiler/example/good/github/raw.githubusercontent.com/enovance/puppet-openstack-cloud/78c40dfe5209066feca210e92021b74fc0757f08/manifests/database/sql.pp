#
# Copyright (C) 2014 eNovance SAS <licensing@enovance.com>
#
# Licensed under the Apache License, Version 2.0 (the "License"); you may
# not use this file except in compliance with the License. You may obtain
# a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
# License for the specific language governing permissions and limitations
# under the License.
#
# MySQL Galera Node
#
# === Parameters
#
#  [*galera_internal_ips*]
#    Array of internal ip of the galera nodes.
#    Defaults to ['127.0.0.1']
#

class cloud::database::sql (
    $api_eth                        = '127.0.0.1',
    $service_provider               = 'sysv',
    $galera_master_name             = 'mgmt001',
    $galera_internal_ips            = ['127.0.0.1'],
    $keystone_db_host               = '127.0.0.1',
    $keystone_db_user               = 'keystone',
    $keystone_db_password           = 'keystonepassword',
    $keystone_db_allowed_hosts      = ['127.0.0.1'],
    $cinder_db_host                 = '127.0.0.1',
    $cinder_db_user                 = 'cinder',
    $cinder_db_password             = 'cinderpassword',
    $cinder_db_allowed_hosts        = ['127.0.0.1'],
    $glance_db_host                 = '127.0.0.1',
    $glance_db_user                 = 'glance',
    $glance_db_password             = 'glancepassword',
    $glance_db_allowed_hosts        = ['127.0.0.1'],
    $heat_db_host                   = '127.0.0.1',
    $heat_db_user                   = 'heat',
    $heat_db_password               = 'heatpassword',
    $heat_db_allowed_hosts          = ['127.0.0.1'],
    $nova_db_host                   = '127.0.0.1',
    $nova_db_user                   = 'nova',
    $nova_db_password               = 'novapassword',
    $nova_db_allowed_hosts          = ['127.0.0.1'],
    $neutron_db_host                = '127.0.0.1',
    $neutron_db_user                = 'neutron',
    $neutron_db_password            = 'neutronpassword',
    $neutron_db_allowed_hosts       = ['127.0.0.1'],
    $mysql_root_password            = 'rootpassword',
    $mysql_sys_maint_password       = 'sys_maint',
    $galera_clustercheck_dbuser     = 'clustercheckdbuser',
    $galera_clustercheck_dbpassword = 'clustercheckpassword',
    $galera_clustercheck_ipaddress  = '127.0.0.1'
) {

  include 'xinetd'

  $gcomm_definition = inline_template('<%= @galera_internal_ips.join(",") + "?pc.wait_prim=no" -%>')

  if $::hostname == $galera_master_name {
    $mysql_service_name = 'mysql-bootstrap'
  } else {
    $mysql_service_name = 'mysql'
  }

  case $::osfamily {
    'RedHat': {
      class { 'mysql':
        server_package_name => 'MariaDB-Galera-server',
        client_package_name => 'MariaDB-client',
        service_name        => $mysql_service_name,
      }

      # Specific to Red Hat
      $wsrep_provider = '/usr/lib64/galera/libgalera_smm.so'

      $dirs = [ '/var/run/mysqld', '/var/log/mysql' ]

      file { $dirs:
        ensure => directory,
        mode   => '0750',
        before => Service['mysqld'],
        owner  => 'mysql'
      }
    } # RedHat
    'Debian': {
      class { 'mysql':
        server_package_name => 'mariadb-galera-server',
        client_package_name => 'mariadb-client',
        service_name        => $mysql_service_name,
      }

      # Specific to Debian / Ubuntu
      $wsrep_provider = '/usr/lib/galera/libgalera_smm.so'

      database_user { 'debian-sys-maint@localhost':
        ensure        => 'present',
        password_hash => mysql_password($mysql_sys_maint_password),
        provider      => 'mysql',
        require       => File['/root/.my.cnf']
      }

      file{'/etc/mysql/debian.cnf':
        ensure  => file,
        content => template('cloud/database/debian.cnf.erb'),
        owner   => 'root',
        group   => 'root',
        mode    => '0600',
        require => Exec['clean-mysql-binlog'],
      }
    } # Debian
    default: {
      err "${::osfamily} not supported yet"
    }
  }

  # This is due to this bug: https://bugs.launchpad.net/codership-mysql/+bug/1087368
  # The backport to API 23 requires a command line option --wsrep-new-cluster:
  # http://bazaar.launchpad.net/~codership/codership-mysql/wsrep-5.5/revision/3844?start_revid=3844
  # and the mysql init script cannot have arguments passed to the daemon
  # using /etc/default/mysql standart mechanism.
  # To check that the mysqld support the options you can :
  # strings `which mysqld` | grep wsrep-new-cluster
  # TODO: to be remove as soon as the API 25 is packaged, ie galera 3 ...
  file { '/etc/init.d/mysql-bootstrap':
    content => template("cloud/database/etc_initd_mysql_${::osfamily}"),
    owner   => 'root',
    mode    => '0755',
    group   => 'root',
    notify  => Service['mysqld'],
    before  => Package['mysql-server'],
  }

  if($::osfamily == 'Debian'){
    # The startup time can be longer than the default 30s so we take
    # care of it there.  Until this bug is not resolved
    # https://mariadb.atlassian.net/browse/MDEV-5540, we have to do it
    # the ugly way.
    file_line { 'debian_increase_mysql_startup_time':
      line    => 'MYSQLD_STARTUP_TIMEOUT=120',
      path    => '/etc/init.d/mysql',
      after   => '^CONF=',
      require => Package['mysql-server'],
      notify  => Service['mysqld'],
    }
  }

  class { 'mysql::server':
    config_hash         => {
      bind_address      => $api_eth,
      root_password     => $mysql_root_password,
      service_name      => $mysql_service_name,
    },
    notify              => Service['xinetd'],
  }

  if $::hostname == $galera_master_name {

# OpenStack DB
    class { 'keystone::db::mysql':
      dbname        => 'keystone',
      user          => $keystone_db_user,
      password      => $keystone_db_password,
      host          => $keystone_db_host,
      allowed_hosts => $keystone_db_allowed_hosts,
    }
    class { 'glance::db::mysql':
      dbname        => 'glance',
      user          => $glance_db_user,
      password      => $glance_db_password,
      host          => $glance_db_host,
      allowed_hosts => $glance_db_allowed_hosts,
    }
    class { 'nova::db::mysql':
      dbname        => 'nova',
      user          => $nova_db_user,
      password      => $nova_db_password,
      host          => $nova_db_host,
      allowed_hosts => $nova_db_allowed_hosts,
    }

    class { 'cinder::db::mysql':
      dbname        => 'cinder',
      user          => $cinder_db_user,
      password      => $cinder_db_password,
      host          => $cinder_db_host,
      allowed_hosts => $cinder_db_allowed_hosts,
    }

    class { 'neutron::db::mysql':
      dbname        => 'neutron',
      user          => $neutron_db_user,
      password      => $neutron_db_password,
      host          => $neutron_db_host,
      allowed_hosts => $neutron_db_allowed_hosts,
    }

    class { 'heat::db::mysql':
      dbname        => 'heat',
      user          => $heat_db_user,
      password      => $heat_db_password,
      host          => $heat_db_host,
      allowed_hosts => $heat_db_allowed_hosts,
    }


# Monitoring DB
    warning('Database mapping must be updated to puppetlabs/puppetlabs-mysql >= 2.x (see: https://dev.ring.enovance.com/redmine/issues/4510)')

    database { 'monitoring':
      ensure  => 'present',
      charset => 'utf8',
      require => File['/root/.my.cnf']
    }
    database_user { "${galera_clustercheck_dbuser}@localhost":
      ensure        => 'present',
      # can not change password in clustercheck script
      password_hash => mysql_password($galera_clustercheck_dbpassword),
      provider      => 'mysql',
      require       => File['/root/.my.cnf']
    }
    database_grant { "${galera_clustercheck_dbuser}@localhost/monitoring":
      privileges => ['all']
    }

    Database_user<<| |>>
  } # if $::hostname == $galera_master

  # Haproxy http monitoring
  file_line { 'mysqlchk-in-etc-services':
    path   => '/etc/services',
    line   => 'mysqlchk 9200/tcp',
    match  => '^mysqlchk 9200/tcp$',
    notify => [ Service['xinetd'], Exec['reload_xinetd'] ]
  }

  file {
    '/etc/xinetd.d/mysqlchk':
      content => template('cloud/database/mysqlchk.erb'),
      owner   => 'root',
      group   => 'root',
      mode    => '0755',
      require => File['/usr/bin/clustercheck'],
      notify  => [ Service['xinetd'], Exec['reload_xinetd'] ];
    '/usr/bin/clustercheck':
      ensure  => present,
      content => template('cloud/database/clustercheck.erb'),
      mode    => '0755',
      owner   => 'root',
      group   => 'root';
  }

  # The puppet-xinetd module do not correctly reload
  # the configuration on “notify”
  # TODO(Gonéri): remove this once https://github.com/puppetlabs/puppetlabs-xinetd/pull/9
  # get merged
  exec{ 'reload_xinetd':
    command     => '/usr/bin/pkill -F /var/run/xinetd.pid --signal HUP',
    refreshonly => true,
    require     => Service['xinetd'],
  }


  exec{'clean-mysql-binlog':
    # first sync take a long time
    command     => "/bin/bash -c '/usr/bin/mysqladmin --defaults-file=/root/.my.cnf shutdown ; /bin/rm  ${::mysql::params::datadir}/ib_logfile*'",
    path        => '/usr/bin',
    require     => [
      File['/root/.my.cnf'],
      Service['mysqld'],
    ],
    notify      => Exec['mysqld-restart'],
    refreshonly => true,
    onlyif      => "stat ${::mysql::params::datadir}/ib_logfile0 && test `du -sh ${::mysql::params::datadir}/ib_logfile0 | cut -f1` != '256M'",
  }

  # TODO/WARNING(Gonéri): template changes do not trigger configuration changes
  mysql::server::config{'basic_config':
    notify_service => true,
    notify         => Exec['clean-mysql-binlog'],
    settings       => template('cloud/database/mysql.conf.erb')
  }

  @@haproxy::balancermember{$::fqdn:
    listening_service => 'galera_cluster',
    server_names      => $::hostname,
    ipaddresses       => $api_eth,
    ports             => '3306',
    options           =>
      inline_template('check inter 2000 rise 2 fall 5 port 9200 <% if @hostname != @galera_master_name -%>backup<% end %>')
  }

}