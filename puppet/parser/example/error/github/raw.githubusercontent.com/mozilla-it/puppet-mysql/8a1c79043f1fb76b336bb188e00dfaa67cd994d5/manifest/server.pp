class mysql::server (
    $cluster   = undef,
    $server_role    = 'slave',
    $wait_timeout = 600,
    $max_connections = 1200,
    $query_cache_type = undef,
    $query_cache_limit = undef,
    $query_cache_size = undef,
    $replicate_wild_do_table = undef,
    $replicate_do_table = undef,
    $innodb_buffer_pool_size = undef,
    $default_storage_engine = undef,
    $performance_schema = undef,
    $table_open_cache = undef,
    $thread_cache_size = undef,
    $binlog_format = undef,
    $expire_logs_days = undef,
    $max_binlog_size = undef,
    $max_allowed_packet = undef,
    $auto_increment_offset = undef,
    $auto_increment_increment = undef,
    $event_scheduler = undef,
    $basedir = undef,
    $service_enable = true,
    $long_query_time = 2,
    $slowlogs=true,
    $slowlogs_logfile = "/var/log/mysql/mysql-slow.log",
    $gtid_mode = undef,
    $enforce_gtid_consistency = undef,
    $master_info_repository = undef,
    ) {
    include mysql::settings

   # node_id is used for the server_id parameter in /etc/my.cnf
   # This uses a fictional function called "make_node_id".
    $node_id = make_node_id($ipaddress);

    if $mysql::settings::package_type == 'mysql56' {
        # remove mariadb repo
        file { '/etc/yum.repos.d/maridb55.repo':
            ensure => absent,
            before => Yumrepo['your-mysql56-repo']
        }

        realize(Yumrepo["your-mysql56-repo"])
     }
  # no need to realize Percona yumrepo for Percona versions because 
  # it's realized for the tools in the client class
    if $mysql::settings::package_type == "mariadb55" {
        realize(Yumrepo["mariadb55"])
    }

# make sure the repos exist, otherwise realizing them will be a problem
    package {
        $mysql::settings::packages:
            ensure          => present,
            require         => $mysql::settings::package_type ? {
                "mysql56"   => Yumrepo["your-mysql56-repo"],
                "mariadb55" => Yumrepo["mariadb55"],
                "percona55" => Yumrepo["percona"],
                "percona51" => Yumrepo["percona"],
                default     => undef,
            }
    }

# grant global auth here - a user for all mysql servers
# for example, a monitoring user
# use a tool like hiera for secrets
        mysql::grant {
            'monitoring':
                username => hiera('secrets_monitoring_mysql_username'),
                username => hiera('secrets_monitoring_mysql_password'),
                database => "*",
                privileges => "PROCESS, REPLICATION CLIENT",
                tables => "*",
                host => 'monitor.example.org';
        }

# if it's not part of a cluster, make a random password for root
# the call to client will store the password in the .my.cnf
    if $cluster == undef {
        $password = md5(fqdn_rand(4294967296))

        exec {
            'root-password':
                unless      => "test -f /root/.my.cnf",
                path => ["/bin", "/usr/bin", "/usr/local/bin"],
                command     => "mysqladmin -u root password \"${password}\"",
                require     => Service[$mysql::settings::service_name],
                before      => Class["mysql::client"];
        }

        class {
            "mysql::client":
                user        => "root",
                password    => $password,
        }
        class { "mysql::client": ;
          user        => "root",
          password    => $password,
        }
    }
    else {
        class {
            "mysql::client": ;
        }
    }

    # handle slow query logs
    # this can be used as an example to handle general logs too
    if ($slowlogs) {
        # make sure slow logs are *actually* enabled at runtime
        # if set, and if not, disable
        mysql::variable {
            'slow_query_log': value => 'ON';
            'slow_query_log_file': value => $slowlogs_logfile;
            'log_output': value => 'FILE';
            'long_query_time': value => $long_query_time;
        }
    } else {
        mysql::variable {
            'slow_query_log': value => 'OFF';
        }
    }

    file {
        '/etc/my.cnf':
            owner => "mysql",
            group => "mysql",
            content => template("mysql/my.cnf.erb"),
            require => Package[$mysql::settings::packages],
            before => Service[$mysql::settings::service_name];
    }

    file {
        '/var/log/mysql':
            ensure => directory,
            owner => 'mysql';
    }

    service {
        $mysql::settings::service_name:
            enable => $service_enable,
            hasrestart => false,
            restart => "/bin/true",
            hasstatus => true,
            require => Package[$mysql::settings::packages];
    }

    if $cluster == undef {
        $motd = "This is a standalone ${server_role} MySQL server."
    } else {
        $motd = "This is a ${server_role} MySQL server for ${cluster}."
    }
    motd {
        'servertype':
            content => "${motd}\n";
    }

}
