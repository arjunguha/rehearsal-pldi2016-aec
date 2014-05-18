# Author: Kumina bv <support@kumina.nl>

# Class: kbp_wordpress::common
#
# Actions:
#  Setup the resources needed for Wordpress that do not require parameters.
#
# Depends:
#  gen_php5::mysql
#  gen_php5::gd
#  gen_php5::curl
#
class kbp_wordpress::common {
  include gen_php5::mysql
  include gen_php5::gd
  include gen_php5::curl
  include kbp_apache::module::expires
  include kbp_apache::module::headers

  file { '/usr/local/bin/fix_wp_permissions':
    content => template('kbp_wordpress/fix_wp_permissions.sh'),
    mode    => 755;
  }
}

# Define: kbp_wordpress
#
# Actions:
#  Setup a wordpress instance.
#
# Parameters:
#  documentroot
#   The documentroot to use. Defaults to '/srv/www/$name'.
#  external_mysql
#   Whether the MySQL for this instance is running on another host. Defaults to true. Requires the remote MySQL to import mysql::server::grant with tag 'mysql_$environment_$custenv_$mysql_tag'.
#  mysql_tag
#   The name for the MySQL server.
#  db
#   The MySQL database
#  user
#   The MySQL user, defaults to $db.
#  password
#   The password for the MySQL user.
#  db_originating_host
#   From which IP address the client will contact the MySQL DB. Defaults to source_ipaddress.
#  serveralias
#   Serveralias for this vhost. Can be an array.
#  access_logformat
#   The format to use for the log. Defaults to combined.
#  monitoring_url
#   The path to use for the monitoring. Defaults to '/'.
#  monitor_statuscode
#   What response status code to expect for monitoring. Defaults to false, which means '200' somewhere down the line.
#  address
#   The address to listen on. Defaults to '*', meaning all addresses.
#  address6
#   The IPv6 address to listen on. Defaults to '::', meaning all addresses.
#  auth
#   Whether the site return a 403 or 401. Defaults to false.
#  monitor
#   Whether to monitor this site. Defaults to true.
#  cron_from_wp
#   If the wp_cron should be called from a system cronjob, set this to false. Otherwise it will assume cron is checked on every page request. Defaults to true.
#  cron_on_host
#   If the cronjob should only be deployed on a specific host, give the hostname here. Can only be one hostname. Defaults to false, to disable this.
#  cron_on_minute
#   The minute entry for cron to determine when to run the cronjob. Defaults to '*/15'.
#  cron_request
#   The path that should be requested by the cron. Defaults to /wp-cron.php?doing_wp_cron.
#  custom_php_ini
#   Whether a custom PHP ini file should be used. If set to true, it'll search at /etc/php5/conf.d/${name}_80/php.ini, so make sure the directory and file exists. Defaults to false.
#  ssl
#   Deploy SSL when set to true. Defaults to false.
#  intermediate
#   The intermediate SSL certificate (chain) to use. Enabling this sets up SSL per the rules from kbp_apache::site. Defaults to false, meaning no intermediate is required.
#  redirect_non_ssl
#   When SSL is deployed, should the non-SSL site redirect to the SSL site? Defaults to true.
#  make_default
#   Whether this site should be shown when someone surfs to the IP address. Defaults to false.
#  ha
#   When this site is a HA site (24x7 support). Defaults to false.
#  admin_ips
#   A list of IPs to which the admin site should be restricted, defaults to false meaning no restrictions
#  admin_error_doc
#   The URL of the error page to display when an IP that is not in admin_ips tries to access the admin page, only used when admin_ips is set, defaults to false meaning standard error page
#  xmlrpc_access
#   Whether we should allow public access to the xmlrpc script. Defaults to true (allow access), set to false to disable access.
#  php
#   How to use php, default to true meaning use fastcgi, other option is 'mod_php'
#  disable_uploads_execute
#   Disallow execution of PHP code in the uploads dir, defaults to false
#  wildcard
#   The wildcard cert to use, setting this will imply ssl=true, defaults to false
#
# Todo:
#  - Allow to export the cronjob to a remote server to be run from there
#  - Allow to use a pacemaker resource to determine where to run the resource.
#
# Depends:
#  kbp_wordpress::common
#  kbp_apache
#  mysql
#
define kbp_wordpress($documentroot="/srv/www/${name}", $external_mysql=true, $mysql_tag=false, $db=false, $user=false, $password, $serveralias=false, $access_logformat="vhostcombined", $monitoring_url='/', $address='*', $address6='::',
    $auth=false, $monitor=true,$monitor_statuscode=false, $cron_from_wp=true, $cron_on_host=false, $cron_on_minute='*/15', $custom_php_ini=false, $intermediate=false, $redirect_non_ssl=true, $make_default=false, $ha=false, $ssl=false,
    $db_originating_host=$source_ipaddress, $admin_ips=false, $admin_error_doc=false, $xmlrpc_access=true, $php=true, $disable_uploads_execute=false, $wildcard=false, $cert=false, $key=false, $cron_request='/wp-cron.php?doing_wp_cron',
    $monitor_response=false, $failover=false) {
  include kbp_wordpress::common

  if $php != true and $php != 'mod_php' {
    fail("Error in config of kbp_wordpress ${name}: \$php should be set to true or 'mod_php', but is set to ${php}")
  }

  $real_tag = $mysql_tag ? {
    false   => "mysql_${environment}_${custenv}",
    default => "mysql_${environment}_${custenv}_${mysql_tag}",
  }
  $real_db = $db ? {
    false   => regsubst($name, '[^a-zA-Z0-9\-_]', '_', 'G'),
    default => $db,
  }
  $real_user = $user ? {
    false   => $real_db,
    default => $user,
  }

  kbp_apache::site { $name:
    documentroot       => $documentroot,
    serveralias        => $serveralias,
    access_logformat   => $access_logformat,
    make_default       => $make_default,
    monitor_path       => $monitoring_url,
    monitor_response   => $monitor_response,
    monitor            => $monitor,
    monitor_statuscode => $monitor_statuscode,
    php                => $php,
    custom_php_ini     => $custom_php_ini,
    address            => $address,
    address6           => $address6,
    auth               => $auth,
    intermediate       => $intermediate,
    ha                 => $ha,
    ssl                => $ssl,
    wildcard           => $wildcard,
    cert               => $cert,
    key                => $key,
    redirect_non_ssl   => $redirect_non_ssl,
    failover           => $failover;
  }

  if $external_mysql {
    if ! defined(Kbp_mysql::Client['dummy']) {
      kbp_mysql::client { 'dummy':
        mysql_tag => $mysql_tag,
        address   => $db_originating_host;
      }
    }

    @@mysql::server::grant { "${real_user} on ${real_db}.* for ${hostname}":
      password => $password,
      tag      => $real_tag,
      hostname => $db_originating_host;
    }
  } else {
    if ! defined(Class['kbp_mysql::server']) {
      class { 'kbp_mysql::server':
        mysql_tag => $mysql_tag;
      }
    }

    if ! defined(Mysql::Server::Grant["${real_user} on ${real_db}.*"]) {
      mysql::server::grant { "${real_user} on ${real_db}.*":
        password => $password;
      }
    }
  }

  # Add default expire headers suitable for Wordpress
  kbp_apache::vhost_addition { "${name}/expires":
    content => template('kbp_wordpress/vhost-additions/expires');
  }

  if $disable_uploads_execute and $php == true {
    kbp_apache::vhost_addition { "${name}/disable_uploads_execute":
      content => "<Location 'wp-content/uploads'>\n  Options -ExecCGI\n</Location>";
    }
  }

  if $admin_ips {
    kbp_apache::vhost_addition { "${name}/admin-access.conf":
      content => template('kbp_wordpress/vhost-additions/admin-access.conf');
    }
  }

  if ! $xmlrpc_access {
    kbp_apache::vhost_addition { "${name}/xmlrpc-access.conf":
      content => template('kbp_wordpress/vhost-additions/xmlrpc-access.conf');
    }
  }

  if ! $cron_from_wp {
    $cronname = regsubst($name, '\.', '-', 'G')

    if (! $cron_on_host) or ($cron_on_host == $hostname) {
      kcron { "${cronname}-wordpress-cronjob":
        command => "/usr/bin/wget -q -O /dev/null http://${name}${cron_request}",
        mailto  => "reports+${environment}@kumina.nl",
        minute  => $cron_on_minute;
      }
    }
  }
}
