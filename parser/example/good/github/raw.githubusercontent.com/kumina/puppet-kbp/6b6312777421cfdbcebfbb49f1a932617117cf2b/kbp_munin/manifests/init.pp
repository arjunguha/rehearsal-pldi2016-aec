# Author: Kumina bv <support@kumina.nl>

#
# Class: kbp_munin::server
#
# Actions:
#  - Install munin (through gen_munin::server)
#  - Install and setup apache
#  - Install and setup rrdcached (when requested)
#
# Parameters:
#  site:
#   The name the munin graphs are hosted on
#  wildcard:
#   The wildcard certificate name (there is no support for separate ssl certs for now)
#  intermediate:
#   The intermediate certificate
#  use_rrdcached:
#   Use rrdcached to cache all writes to RRD
#  allowed_access_to_root:
#   By default, access to the root of the site (the overview) is disallowed. When this parameter is set,
#   the people in it's environment are allowed access to the root and are able to see an overview of all machines.
#  async_key:
#   The private key to use for ssh communication.
#  async_pub_key:
#   The public key to export for ssh communication.
#
# Depends:
#  gen_munin::server
#
class kbp_munin::server ($site, $wildcard=false, $intermediate=false, $use_rrdcached=true, $allowed_access_to_root='kumina', $async_key=false, $async_pub_key=false){
  include gen_munin::server

  if $wildcard {
    $port = 443
    include kbp_apache::ssl
  } else {
    $port = 80
  }


  file {
    '/etc/munin/munin.conf':
      content => template('kbp_munin/munin.conf'),
      require => Package['munin'];
    '/etc/munin/conf':
      ensure  => directory,
      purge   => true,
      recurse => true,
      require => Package['munin'];
    '/etc/apache2/conf.d/munin':
      ensure  => absent,
      require => Package['munin'],
      notify  => Exec['reload-apache2'];
    '/etc/cron.d/munin':
      ensure  => absent,
      require => Package['munin'],
      notify  => Exec['reload-cron'];
  }

  # Backups
  file { '/etc/backup/prepare.d/pack-munin-rrds':
    content => template('kbp_munin/pack-munin-rrds.sh'),
    mode    => 750;
  }

  kbp_backup::exclude { '/var/lib/munin':; }

  kcron {
    'munin-update':
      user    => 'munin',
      command => '/usr/share/munin/munin-update',
      minute  => '*/5',
      require => Package['munin'];
    'munin-html':
      user    => 'munin',
      command => '/usr/share/munin/munin-limits ; /usr/bin/nice /usr/share/munin/munin-html',
      minute  => '1',
      require => Package['munin'];
    'munin-limits':
      user    => 'munin',
      command => '/usr/share/munin/munin-limits --force --contact nagios --contact old-nagios',
      minute  => '14',
      hour    => '10',
      require => Package['munin'];
    'munin-rrd-cleanup':
      user    => 'munin',
      command => '/usr/bin/find /var/lib/munin -name *.rrd -type f -mtime +14 -delete',
      minute  => '15',
      hour    => '2';
  }

  kbp_apache::site { $site:
    make_default => true,
    wildcard     => $wildcard,
    intermediate => $intermediate,
    auth         => true;
  }

  kbp_apache::vhost_addition {
    "${site}/munin.conf":
      ports   => $port,
      content => template("kbp_munin/apache2/munin.conf");
    # Configure access to the root web-dir
    "${site}/access_0_common":
      ports   => $port,
      content => template("kbp_munin/apache2/access_common");
  }

  kbp_apache::cgi { "${site}_${port}":
    set_scriptalias => false;
  }

  File <| title == "/srv/www/${site}" |> {
    mode => 775,
  }

  setfacl { "/srv/www/${site} munin access":
    acl          => "group:munin:rwx",
    dir          => "/srv/www/${site}",
    make_default => true,
    require      => [Kbp_apache::Site[$site],Package['munin']];
  }

  if $use_rrdcached {
    # rrdcached makes for less IO on the machine
    kservice {"rrdcached":
      hasreload => false;
    }
    group { "rrdcached":
      system => true,
      ensure => present;
    }
    user { ["www-data", "munin"]:
      groups  => "rrdcached",
      require => [Package["munin","apache2"], Group["rrdcached"]];
    }
    file { "/etc/default/rrdcached":
      content => template("kbp_munin/rrdcached.default"),
      require => Package["rrdcached"],
      notify  => Exec["reload-rrdcached"];
    }

    gen_munin::client::plugin { 'rrdcached':
      script_path => '/usr/share/munin/plugins/kumina';
    }

    gen_munin::client::plugin::config { 'rrdcached':
      content => 'user root';
    }
  }

  if $async_key {
    file {
      ['/var/lib/munin/.ssh','/var/lib/munin/.ssh/tmp']:
        ensure  => directory,
        owner   => 'munin',
        mode    => 700,
        require => Package['munin-async'];
      '/var/lib/munin/.ssh/id_rsa':
        content => $async_key,
        mode    => 700,
        owner   => 'munin';
      '/var/lib/munin/.ssh/config':
        content => "Host *\n UserKnownHostsFile=/dev/null\n StrictHostKeyChecking=no\n",
        owner   => 'munin';
    }

    @@ssh_authorized_key { "Munin-async access from ${hostname}":
      key     => $async_pub_key,
      type    => 'ssh-rsa',
      options => ['no-port-forwarding','no-X11-forwarding','no-agent-forwarding','no-pty','no-user-rc',"from=\"${fqdn}\"",'command="/usr/share/munin/munin-async --spoolfetch"'],
      user    => 'munin-async',
      require => Package['munin-async'],
      tag     => 'munin-server-access',
    }

    Kbp_munin::Async::Environment <<| |>> {
      site => $site,
      port => $port,
    }
  } else {
    Kbp_munin::Environment <<| |>> {
      site => $site,
      port => $port,
    }
  }
}

#
# Define: kbp_munin::environment
#
# Actions:
#  - Add apache config for the environment
#  - Import htpasswd info
#  - Export config for the clients
#
# Depends:
#  gen_puppet
#
define kbp_munin::environment ($site = false, $port = false, $prettyname) {
  gen_munin::environment{$name:;}

  kbp_apache::vhost_addition { "${site}/access_${name}":
    ports   => $port,
    content => template("kbp_munin/apache2/access.conf");
  }

  concat { "/srv/www/${site}/.htpasswd_${name}":
    require => File["/srv/www/${site}"];
  }

  Concat::Add_content <<| tag == "htpasswd_${name}" |>> {
    target => "/srv/www/${site}/.htpasswd_${name}",
  }

  kbp_ferm::rule { "Munin connections for ${name}":
    saddr    => $ipaddress,
    proto    => "tcp",
    dport    => "4949",
    action   => "ACCEPT",
    exported => true,
    ferm_tag => "trending_${name}";
  }
}

#
# Define: kbp_munin::environment
#
# Actions:
#  - Add apache config for the environment
#  - Import htpasswd info
#  - Export config for the clients
#
# Depends:
#  gen_puppet
#
define kbp_munin::async::environment($site=false, $port=false, $prettyname) {
  gen_munin::async::environment{$name:;}

  kbp_apache::vhost_addition { "${site}/access_${name}":
    ports   => $port,
    content => template("kbp_munin/apache2/access.conf");
  }

  concat { "/srv/www/${site}/.htpasswd_${name}":
    require => File["/srv/www/${site}"];
  }

  Concat::Add_content <<| tag == "htpasswd_${name}" |>> {
    target => "/srv/www/${site}/.htpasswd_${name}",
  }
}

#
# Class: kbp_munin::client
#
# Actions: Install munin-node (through gen_munin) and import config
#
# Depends:
#  kbp_munin
#  gen_munin::client
#
class kbp_munin::client($ensure='present') {
  class { 'gen_munin::client':
    ensure => $ensure;
  }

  package { 'munin-plugins-kumina':
    notify => $ensure ? {
      'present' => Service['munin-node'],
      'absent'  => undef,
    },
    ensure => $ensure ? {
      'present' => 'latest',
      'absent'  => 'absent',
    };
  }

  package { 'munin-async':
    ensure => purged;
  }

  if $ensure == 'present' {
    Kbp_ferm::Rule <<| tag == "trending_${environment}" |>>
  }

  # Easily switch back to non-async
  file { '/etc/cron.d/restart-munin-async':
    ensure => absent;
  }
}

# Class: kbp_munin::async_client
#  Actions: Set an asynchronous client up.
#
class kbp_munin::async_client($ensure='present') {
  class { 'gen_munin::async_client':
    ensure => $ensure;
  }

  package { 'munin-plugins-kumina':
    notify => $ensure ? {
      'present' => Service['munin-node'],
      'absent'  => undef,
    },
    ensure => $ensure ? {
      'present' => 'latest',
      'absent'  => 'absent',
    };
  }

  if $ensure == 'present' {
    Ssh_authorized_key <<| tag == 'munin-server-access' |>>
  }

  # Async daemon seems to stop all of a sudden on a regular basis. Let's restart until we can fix this.
  kcron { 'restart-munin-async':
    ensure  => $ensure,
    command => '/usr/sbin/service munin-async restart >/dev/null',
    mailto  => "reports+${environment}@kumina.nl",
    hour    => '0',
    minute  => '2';
  }
}

# Class: kbp_munin::client::activemq
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_munin::client::activemq {
  gen_munin::client::plugin { ["activemq_size", "activemq_subscribers", "activemq_traffic"]:
    script_path => "/usr/share/munin/plugins/kumina",
    script      => "activemq_";
  }
}

# Class: kbp_munin::client::drbd
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_munin::client::drbd {
  gen_munin::client::plugin { ["drbd_net_0", "drbd_disk_0"]:
    script_path => "/usr/share/munin/plugins/kumina",
    script      => "drbd_";
  }
}

# Class: kbp_munin::client::apache
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_munin::client::apache {
  # This class is should be included in kbp_apache to collect apache data for munin
  include gen_base::libwww-perl

  gen_munin::client::plugin {
    "apache_accesses":;
    "apache_processes":;
    "apache_volume":;
  }

  gen_munin::client::plugin::config { "apache_":
    section => 'apache_*',
    content => "env.url http://127.0.0.255:%d/server-status?auto\nenv.ports 80";
  }

}

# Class: kbp_munin::client::fail2ban
#
# Actions:
#  Trend fail2ban.
#
class kbp_munin::client::fail2ban {
  gen_munin::client::plugin {
    'fail2ban':;
  }
}

# Class: kbp_munin::client::haproxy
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_munin::client::haproxy {
  gen_munin::client::plugin { ["haproxy_check_duration","haproxy_errors","haproxy_sessions","haproxy_volume"]:
    script_path => "/usr/share/munin/plugins/kumina",
  }

  gen_munin::client::plugin::config { "haproxy_":
    section => "haproxy_*",
    content => "user root\nenv.socket /var/run/haproxy.sock";
  }
}

# Class: kbp_munin::client::icinga
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_munin::client::icinga {
  gen_munin::client::plugin { ["icinga_multi_hosts","icinga_multi_services","icinga_multi_checks"]:
    script_path => "/usr/share/munin/plugins/kumina",
    script      => "icinga_multi_";
  }

  gen_munin::client::plugin::config { "icinga_multi_":
    section => "icinga_multi_*",
    content => "user root";
  }
}

# Class: kbp_munin::client::memcached
#
# Actions:
#  Setup memcached plugins.
#
class kbp_munin::client::memcached {
  include gen_base::libcache_memcached_perl

  gen_munin::client::plugin { ['memcached_bytes','memcached_rates','memcached_counters']:
    script      => "memcached_";
  }

  gen_munin::client::plugin::config { "memcached":
    section => "memcached_*",
    content => "env.host 127.0.0.1\nenv.port 11211\nenv.timescale 3\n";
  }
}

# Class: kbp_munin::client::puppetmaster
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_munin::client::puppetmaster {
  gen_munin::client::plugin {
    ["puppet_nodes","puppet_totals"]:
      script_path => "/usr/share/munin/plugins/kumina",
      script      => "puppet_";
  }

  gen_munin::client::plugin::config { "puppet_":
    section => "puppet_*",
    content => "user root\nenv.num_minutes 60,360";
  }
}

# Class: kbp_munin::client::mysql
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_munin::client::mysql {
  if versioncmp($lsbdistrelease, 6) >= 0 {
    package {"libcache-cache-perl":
      ensure => latest;
    }

    munin_mysql {["bin_relay_log","commands","connections",
      "files_tables","innodb_bpool","innodb_bpool_act",
      "innodb_insert_buf","innodb_io","innodb_io_pend",
      "innodb_log","innodb_rows","innodb_semaphores",
      "innodb_tnx","myisam_indexes","network_traffic",
      "qcache","qcache_mem","replication","select_types",
      "slow","sorts","table_locks","tmp_tables"]:;
    }

    # Remove the old plugins, since they error for strange reasons
    file { ["/etc/munin/plugins/mysql_bytes","/etc/munin/plugins/mysql_innodb",
      "/etc/munin/plugins/mysql_queries","/etc/munin/plugins/mysql_threads",
      "/etc/munin/plugins/mysql_slowqueries"]:
      ensure => absent,
      notify => Service["munin-node"],
    }
  } elsif versioncmp($lsbdistrelease, 6) < 0 {
    gen_munin::client::plugin { ["mysql_bytes","mysql_innodb","mysql_queries","mysql_slowqueries","mysql_threads"]:;  }
  }

  define munin_mysql {
    gen_munin::client::plugin { "mysql_${name}":
      script => "mysql_";
    }
  }
}

# Class: kbp_munin::client::nfs
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_munin::client::nfs {
  gen_munin::client::plugin { "nfs_client":; }
}

# Class: kbp_munin::client::nfsd
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_munin::client::nfsd {
  gen_munin::client::plugin { "nfsd":; }
}

# Class: kbp_munin::client::ntpd
#
# Actions:
#  Setup trending for ntpd.
#
# Depends:
#  kbp_munin::client
#  gen_munin::client::plugin
#  gen_puppet
#
class kbp_munin::client::ntpd {
  gen_munin::client::plugin { ["ntp_kernel_err","ntp_kernel_pll_freq","ntp_kernel_pll_off","ntp_offset",'ntp_states']:; }
}

# Class: kbp_munin::client::postgresql
#
# Actions:
#  Setup trending of PostgreSQL.
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_munin::client::postgresql {
  gen_munin::client::plugin { ["postgres_bgwriter","postgres_checkpoints","postgres_connections_db","postgres_users","postgres_xlog"]:; }

  gen_munin::client::plugin::config { "postgres_*":
    content => "user postgres",
  }

  kbp_munin::client::postgresql_dbs { "ALL":; }
}

# Define: kbp_munin::client::postgresql_dbs
#
# Actions:
#  Setup trending of PostgreSQL databases. Requires the settings from kbp_munin::client::postgresql.
#
# Parameters:
#  name
#   The database to setup trending for.
#
# Depends:
#  kbp_munin::client::postgresql
#  gen_puppet
#
define kbp_munin::client::postgresql_dbs {
  if $name != 'template0' and $name != 'template1' {
    gen_munin::client::plugin {
      "postgres_cache_${name}":
        script => "postgres_cache_";
      "postgres_locks_${name}":
        script => "postgres_locks_";
      "postgres_querylength_${name}":
        script => "postgres_querylength_";
      "postgres_scans_${name}":
        script => "postgres_scans_";
      "postgres_size_${name}":
        script => "postgres_size_";
      "postgres_transactions_${name}":
        script => "postgres_transactions_";
      "postgres_tuples_${name}":
        script => "postgres_tuples_";
    }
  }
}

# Class: kbp_munin::client::powerdns
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_munin::client::powerdns {
  gen_munin::client::plugin { ['pdns_errors','pdns_latency','pdns_qsize','pdns_queries']:
    script_path => '/usr/share/munin/plugins/kumina';
  }

  gen_munin::client::plugin::config { 'pdns':
    section => 'pdns_*',
    content => "user root\n";
  }
}

# Class: kbp_munin::client::bind9
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_munin::client::bind9 {
  gen_munin::client::plugin { "bind9_rndc":; }

  gen_munin::client::plugin::config { "bind9_rndc":
    content => "env.querystats /var/cache/bind/named.stats\nuser bind",
  }
}

# Class: kbp_munin::client::unbound
#
# Actions:
#  setup trending for unbound
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_munin::client::unbound {
  gen_munin::client::plugin { ["unbound_hits", "unbound_queue", "unbound_memory", "unbound_by_type", "unbound_by_opcode", "unbound_by_rcode", "unbound_by_flags", "unbound_histogram"]:
    script_path => "/usr/share/munin/plugins/kumina",
    script      => "unbound_";
  }

  gen_munin::client::plugin::config { "unbound":
    section => "unbound*",
    content => "user root\nenv.statefile /tmp/munin-unbound-state\nenv.unbound_conf /etc/unbound/unbound.conf\nenv.unbound_control /usr/sbin/unbound-control\nenv.spoof_warn 1000\nenv.spoof_crit 100000",
  }
}

# Class: kbp_munin::client::glassfish
#
# Actions:
#  Setup the munin trending for glassfish
#
# Depends:
#  kbp_munin::client
#  gen_puppet
#
class kbp_munin::client::glassfish {
  gen_munin::client::plugin { "files_user_glassfish":
    script_path => '/usr/share/munin/plugins/kumina',
    script      => 'files_user_';
  }
}

# Define: kbp_munin::client::glassfish_instance
#
# Actions:
#  Setup the munin trending for glassfish domains
#
# Depends:
#  kbp_munin::client
#  gen_puppet
#
define kbp_munin::client::glassfish_instance ($jmxport, $jmxuser=false, $jmxpass=false) {
  kbp_munin::client::jmxcheck { ["${name}_${jmxport}_java_threads", "${name}_${jmxport}_java_process_memory", "${name}_${jmxport}_java_cpu"]:
      jmxuser => $jmxuser,
      jmxpass => $jmxpass;
  }

  # GC plugin doesn't work glassfish
  file { ["/etc/munin/plugins/${name}_${jmxport}_gc_collectioncount", "/etc/munin/plugins/${name}_${jmxport}_gc_collectiontime"]:
    ensure => absent;
  }
}

# Define: kbp_munin::client::jmxcheck
#
# Actions:
#  install the link with the right name in /etc/munin/plugins using gen_munin::client::plugin { }
#
# Depends:
#  gen_puppet
#  gen_munin::client
#
define kbp_munin::client::jmxcheck ($jmxuser=false, $jmxpass=false){
  include gen_base::jmxquery

  gen_munin::client::plugin { "jmx_${name}":
    script_path => "/usr/share/munin/plugins/kumina",
    script      => "jmx_",
    require     => Package["jmxquery","munin-plugins-kumina"];
  }

  if $jmxuser {
    gen_munin::client::plugin::config { "jmx_${name}":
      content => "env.jmxuser ${jmxuser}\nenv.jmxpass ${jmxpass}";
    }
  }
}

class kbp_munin::client::tomcat ($trending_password) {
  include gen_base::libxml_simple_perl
  gen_munin::client::plugin { ['tomcat_access','tomcat_jvm','tomcat_threads','tomcat_volume']:; }

  gen_munin::client::plugin { "files_user_tomcat6":
    script_path => '/usr/share/munin/plugins/kumina',
    script      => 'files_user_';
  }

  gen_munin::client::plugin { ['tomcat_avgtime','tomcat_maxtime']:
    script      => 'tomcat_';
  }

  gen_munin::client::plugin::config { 'tomcat':
    section => 'tomcat_*',
    content => "env.timeout 10\nenv.ports 8080\nenv.user munin\nenv.password ${trending_password}";
  }
}

class kbp_munin::client::samba {
  gen_munin::client::plugin { 'samba':; }
}
