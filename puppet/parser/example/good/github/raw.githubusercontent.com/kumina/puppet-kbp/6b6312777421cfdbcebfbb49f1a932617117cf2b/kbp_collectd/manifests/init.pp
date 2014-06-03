class kbp_collectd {
  include gen_collectd
  include kbp_icinga::collectd
}

class kbp_collectd::base {
  if $lsbdistcodename == 'lenny' {
    notify { 'Sorry, no collectd for lenny!':; }
  } else {
    include kbp_collectd
    include gen_collectd::plugin::df

    gen_collectd::plugin {
      ['contextswitch', 'cpu', 'conntrack', 'entropy', 'load', 'memory',
      'numa', 'processes', 'swap', 'uptime', 'users', 'vmem', 'tcpconns']:;
      'interface':
        pluginconf => { 'Interface' => 'lo', 'IgnoreSelected' => true };
    }

    gen_collectd::python_plugin { ['iostat', 'used_inodes', 'used_file_descriptors']:; }
  }
}

define kbp_collectd::plugin::network ($listen=false, $server=false, $source_ip=$source_ipaddress, $forward=false, $server_collectd_tag="collectd_${environment}_${custenv}", $server_encrypt = true, $listen_collectd_tag="collectd_${environment}_${custenv}") {
  if $lsbdistcodename != 'lenny' {
    include kbp_collectd

    if $listen {
      concat { "/etc/collectd/auth_${listen_collectd_tag}":
        mode => 600
      }
      Concat::Add_content <<| tag == $listen_collectd_tag |>>
      Kbp_ferm::Rule <<| tag == $listen_collectd_tag |>>
    }

    if $server {
      if $server_encrypt {
        $password = generate("/usr/local/bin/collectd_puppet", $fqdn, 'collectd')
        $auth_string = "${fqdn}: $password"

        @@concat::add_content { "collectd_credentials_${fqdn}":
          content => $auth_string,
          target  => "/etc/collectd/auth_${server_collectd_tag}",
          tag     => $server_collectd_tag;
        }
      }

      kbp_ferm::rule { "Collectd access ${name}":
        exported => true,
        proto    => 'udp',
        dport    => 25826,
        saddr    => $source_ip,
        action   => "ACCEPT",
        ferm_tag => $server_collectd_tag;
      }
    }

    # uglyness galore!
    $pluginconf = parsejson(template('kbp_collectd/network'))
    gen_collectd::plugin { $name:
      plugin     => 'network',
      pluginconf => $pluginconf;
    }
  }
}

class kbp_collectd::plugin::apache {
  if defined(Class['kbp_collectd']) {
    gen_collectd::plugin {
      'apache':
        pluginconf => {'Instance ""' => {'URL' => "http://127.0.0.255/server-status?auto"} };
      'processes_apache2':
        plugin       => 'processes',
        noloadplugin => true;
    }
  }
}

class kbp_collectd::plugin::memcached {
  if defined(Class['kbp_collectd']) {
    gen_collectd::plugin { 'memcached':; }
  }
}

class kbp_collectd::plugin::nfs {
  if defined(Class['kbp_collectd']) {
    gen_collectd::plugin { 'nfs':; }
  }
}

class kbp_collectd::plugin::libvirt {
  if defined(Class['kbp_collectd']) {
    gen_collectd::plugin { 'libvirt':
      pluginconf => { 'Connection' => 'qemu:///system' };
    }
  }
}

class kbp_collectd::plugin::varnish {
  if defined(Class['kbp_collectd']) {
    gen_collectd::plugin { 'varnish':
      pluginconf => { 'Instance ""' => {'CollectCache' => 'true',
                                        'CollectConnections' => 'true',
                                        'CollectBackend' => 'true',
                                        'CollectSHM' => 'true',
                                        'CollectESI' => 'true',
                                        'CollectFetch' => 'true',
                                        'CollectHCB' => 'true',
                                        'CollectSMS' => 'true',
                                        'CollectTotals' => 'true',
                                        'CollectWorkers' => 'true'}};
    }
  }
}

class kbp_collectd::plugin::drbd {
  if defined(Class['kbp_collectd']) {
    gen_collectd::python_plugin { 'drbd':; }
  }
}

class kbp_collectd::plugin::activemq {
  if defined(Class['kbp_collectd']) {
    gen_collectd::python_plugin { 'activemq':; }
  }
}

class kbp_collectd::plugin::tomcat($monitor_password) {
  if defined(Class['kbp_collectd']) {
    gen_collectd::plugin {
      'tomcat':
        plugin       => 'java',
        content      => template('kbp_collectd/tomcat');
      'processes_tomcat':
        plugin       => 'processes',
        noloadplugin => true;
    }
  }
}

class kbp_collectd::plugin::postgres {
  if defined(Class['kbp_collectd']) {
    gen_collectd::plugin { 'postgres':
      content => template('kbp_collectd/postgres');
    }
  }
}

class kbp_collectd::plugin::haproxy {
  if defined(Class['kbp_collectd']) {
    gen_collectd::python_plugin { 'haproxy':; }

    gen_collectd::plugin { 'processes_haproxy':
      plugin       => 'processes',
      noloadplugin => true;
    }
  }
}

class kbp_collectd::plugin::icinga {
  if defined(Class['kbp_collectd']) {
    gen_collectd::python_plugin { 'icinga':; }
  }
}

class kbp_collectd::plugin::postfix {
  if defined(Class['kbp_collectd']) {
    gen_collectd::python_plugin { 'postfix':; }
  }
}

class kbp_collectd::plugin::php_apc {
  if defined(Class['kbp_collectd']) {
    gen_collectd::python_plugin { 'php_apc':; }
  }
}

class kbp_collectd::plugin::unbound {
  if defined(Class['kbp_collectd']) {
    gen_collectd::python_plugin { 'unbound':; }
  }
}

class kbp_collectd::plugin::powerdns {
  if defined(Class['kbp_collectd']) {
    gen_collectd::plugin { 'powerdns':
      content => template('kbp_collectd/conf/powerdns');
    }
  }
}

class kbp_collectd::plugin::mysql($mysql_tag) {
  if defined(Class['kbp_collectd']) {
    $collectd_mysql_password = generate("/usr/local/bin/collectd_puppet", $mysql_tag, 'mysql')
    if defined(Class['kbp_mysql::mastermaster']) or defined(Class['kbp_percona::mastermaster']) {
      class { 'kbp_collectd::plugin::mysql::setup_super':
        collectd_mysql_password => $collectd_mysql_password;
      }
      gen_collectd::plugin { 'mysql':
        pluginconf => {'Database "localhost"' => { 'User' => 'collectd', 'Password' => $collectd_mysql_password, 'MasterStats' => true, 'SlaveStats' => true}};
      }
    } elsif defined(Class['kbp_mysql::master']) or defined(Class['kbp_percona::master']) {
      class { 'kbp_collectd::plugin::mysql::setup_super':
        collectd_mysql_password => $collectd_mysql_password;
      }
      gen_collectd::plugin { 'mysql':
        pluginconf => {'Database "localhost"' => {'User' => 'collectd', 'Password' => $collectd_mysql_password, 'MasterStats' => true}};
      }
    } elsif defined(Class['kbp_mysql::slave']) or defined(Class['kbp_percona::slave']) {
      gen_collectd::plugin { 'mysql':
        pluginconf => {'Database "localhost"' => {'User' => 'collectd', 'Password' => $collectd_mysql_password, 'SlaveStats' => true}};
      }
    } else { # A normal server
      if defined(Class['kbp_percona::server']) {
        gen_percona::user { "collectd":
          user     => 'collectd',
          password => $collectd_mysql_password;
        }
      }
      if defined(Class['kbp_mysql::server']) {
        mysql::user { "collectd":
          user     => 'collectd',
          password => $collectd_mysql_password;
        }
      }
      gen_collectd::plugin { 'mysql':
        pluginconf => {'Database "localhost"' => {'User' => 'collectd', 'Password' => $collectd_mysql_password}};
      }
    }
  }
}

class kbp_collectd::plugin::mysql::setup_super($collectd_mysql_password) {
  notify { $collectd_mysql_password:; }
  if defined(Class['kbp_percona::server']) {
    gen_percona::server::grant { "collectd_super_privs":
      user        => "collectd",
      db          => "*",
      password    => $collectd_mysql_password,
      permissions => "super, replication client";
    }
  }
  if defined(Class['kbp_mysql::server']) {
    mysql::server::grant { "collectd_super_privs":
      user        => "collectd",
      db          => "*",
      password    => $collectd_mysql_password,
      permissions => "super, replication client";
    }
  }
}
