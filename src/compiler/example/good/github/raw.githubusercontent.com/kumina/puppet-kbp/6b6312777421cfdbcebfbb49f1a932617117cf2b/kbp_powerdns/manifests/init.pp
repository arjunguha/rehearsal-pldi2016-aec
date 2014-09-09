# Author: Kumina bv <support@kumina.nl>

# Class: kbp_powerdns::authoritative::master
#
# Actions: Install the PowerDNS authoritative server and setup MySQL in mastermode. It also adds users and permissions to the database.
#
# Parameters:
#  db_password      The password for the pdns user (which has read-only) access
#  ssl_certlocation The location of the SSL certificate/key
#  ssl_intermediate The name of the intermediate certificate
#  admin_password   The password for the read/write pdns_admin user
#  mysql_tag        The tag for this MySQL cluster
#  localaddress     The address where PowerDNS should bind
#  auth_servers     A comma-separated (no spaces) list of the names of the authoritative servers for this cluster (needed for the icinga checks)
#
# Depends:
#  kbp_powerdns::authoritative
#
class kbp_powerdns::authoritative::master ($db_password, $certlocation, $intermediate, $admin_password, $pdns_tag="pdns_${environment}", $localaddress=$::external_ipaddress, $localport=53, $localaddress6=$::external_ipaddress_v6, $auth_servers=false) {
  class {
    'kbp_powerdns::authoritative':
      localaddress  => $localaddress,
      localaddress6 => $localaddress6,
      localport     => $localport,
      pdns_tag      => $pdns_tag;
    'kbp_mysql::master':
      mysql_tag    => $pdns_tag;
    'kbp_mysql::server::ssl':
      certlocation => $certlocation,
      intermediate => $intermediate;
  }

  mysql::server::grant {
    'pdns_admin on pdns':
      permissions => 'select, insert, update, delete',
      password    => $admin_password;
    'pdns on pdns':
      permissions => 'select',
      password    => $db_password;
  }

  Mysql::Server::Grant <<| tag == $pdns_tag |>>

  file {
    '/etc/powerdns/admin':
      ensure  => directory,
      require => Package['pdns-server'];
    '/etc/powerdns/admin/pdns.conf':
      content => template('kbp_powerdns/admin_pdns.conf'),
      mode    => 440;
  }

  # This export is imported by ALL kbp_powerdns::authoritative imports to configure its database settings.
  @@gen_powerdns::backend::mysql { $pdns_tag:
    db_password => $db_password;
  }

  @@host { $fqdn:
    ip  => $external_ipaddress,
    tag => $pdns_tag;
  }

  Kbp_ferm::Rule <<| tag == $pdns_tag |>>

  if $auth_servers {
    $zones = split($::pdns_zones,',')

    kbp_icinga::dnszones::auth { $zones:
      authoritative_servers => $auth_servers;
    }
  }
}

# Class: kbp_powerdns::authoritative::slave
#
# Actions: Install the PowerDNS authoritative server and setup MySQL in slavemode.
#
# Parameters:
#  repl_password    The password for the pdns_repl user
#  ssl_intermediate The name of the intermediate certificate
#  mysql_tag        The tag for this MySQL cluster
#  localaddress     The address where PowerDNS should bind
#
# Depends:
#  kbp_powerdns::authoritative
#
class kbp_powerdns::authoritative::slave ($repl_password, $intermediate, $pdns_tag="pdns_${environment}", $localaddress=$::external_ipaddress, $localaddress6=$::external_ipaddress_v6, $localport=53){
  include "kbp_ssl::intermediate::${intermediate}"
  class {
    'kbp_powerdns::authoritative':
      localaddress     => $localaddress,
      localaddress6    => $localaddress6,
      localport        => $localport,
      pdns_tag         => $pdns_tag;
    'kbp_mysql::slave':
      mysql_tag        => $pdns_tag,
      repl_user        => 'pdns_repl',
      repl_password    => $repl_password,
      repl_require_ssl => true,
      bind_address     => '127.0.0.1',
      setup_backup     => false;
  }

  Host <<| tag == $pdns_tag |>>
}

# Class: kbp_powerdns::authoritative
#
# Actions: Install the PowerDNS authoritative server and setup monitoring/trending
#
# Parameters:
#  localaddress     The address where PowerDNS should bind (multiple addresses should be space-separated)
#
# Depends:
#  gen_powerdns
#
class kbp_powerdns::authoritative ($localaddress, $localaddress6=false, $localport=53, $pdns_tag="pdns_${environment}") {
  include kbp_munin::client::powerdns
  include kbp_collectd::plugin::powerdns
  include kbp_icinga::dnszones::pdns
  class { 'gen_powerdns':
    localaddress  => $localaddress,
    localport     => $localport,
    localaddress6 => $localaddress6;
  }

  Gen_powerdns::Backend::Mysql <<| title == $pdns_tag |>>

  if $localaddress != '127.0.0.1' {
    kbp_ferm::rule { 'PowerDNS_v4':
      proto  => '(tcp udp)',
      daddr  => "(${localaddress})",
      dport  => 53,
      action => ACCEPT;
    }
  }

  if $localaddress6 {
    kbp_ferm::rule { 'PowerDNS_v6':
      proto  => '(tcp udp)',
      daddr  => "(${localaddress6})",
      dport  => 53,
      action => ACCEPT;
    }
  }

  kbp_icinga::proc_status { 'pdns':; }
}

# Class: kbp_powerdns::admin
#
# Actions: Setup a Django site for the pdns-manager application
#
# Parameters:
#  intermediate  The intermediate certificate
#  cert          The certificate used for the site
#  wildcard      The wildcard certificate for this site
#  monitor_proxy The proxy that should be used to monitor the site
#  db_saddr      The source address the webserver uses to connect to the database
#  db_saddr6     Idem, IPv6
#  db_hostname   The hostname of the webserver (for MySQL grant)
#  pdns_tag      The tag for the pdns server used
#
define kbp_powerdns::admin ($admin_password, $site_address='*', $intermediate=false, $cert=false, $wildcard=false, $pdns_tag="pdns_${environment}", $monitor_proxy=false, $db_saddr=$external_ipaddress, $db_saddr6=$external_ipaddress_v6, $db_hostname=$fqdn) {
  include gen_base::python_mysqldb
  include gen_base::python-dnspython

  kbp_ferm::rule { "pdns_admin access for ${name}":
    saddr    => $db_saddr,
    dport    => 3306,
    proto    => tcp,
    exported => true,
    action   => 'ACCEPT',
    ferm_tag => $pdns_tag;
  }

  @@mysql::server::grant { "pdns_admin on pdns from ${fqdn} for ${name}":
    permissions => 'select, insert, update, delete',
    user        => 'pdns_admin',
    db          => 'pdns',
    password    => $admin_password,
    hostname    => $db_hostname,
    require_ssl => true,
    tag         => $pdns_tag;
  }

  if $db_saddr6 {
    kbp_ferm::rule { "pdns_admin access for ${name} (IPv6)":
      saddr    => $db_saddr6,
      dport    => 3306,
      proto    => tcp,
      exported => true,
      action   => 'ACCEPT',
      ferm_tag => $pdns_tag;
    }

    @@mysql::server::grant { "pdns_admin on pdns from ${fqdn} for ${name} (IPv6)":
      permissions => 'select, insert, update, delete',
      user        => 'pdns_admin',
      db          => 'pdns',
      password    => $admin_password,
      hostname    => $db_saddr6,
      require_ssl => true,
      tag         => $pdns_tag;
    }
  }

  kbp_django::site { $name:
    address       => $site_address,
    cert          => $cert,
    intermediate  => $intermediate,
    wildcard      => $wildcard,
    monitor_path  => '/admin/',
    monitor_proxy => $monitor_proxy;
  }

  if $cert or $intermediate or $wildcard {
    $ssl = true
  }

  kbp_apache::vhost_addition {
    "${name}/static":
      ports   => $ssl ? {
        true    => 443,
        default => 80,
      },
      content => "Alias /static /usr/share/pyshared/django/contrib/admin/static/\n";
    "${name}/zz-redirect":
      ports   => $ssl ? {
        true    => 443,
        default => 80,
      },
      content => "RewriteEngine On\nRewriteRule ^/$ /admin [R=301,L]";
  }
}
