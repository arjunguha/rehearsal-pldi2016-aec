# Author: Kumina bv <support@kumina.nl>

# Class: kbp_dovecot::imap
#
# Actions:
#  Setup an IMAP server with Sieve, which uses a MySQL backend for domain and user settings. The MySQL database should contain three tables, defined as follows:
#   CREATE TABLE `mail_aliases` (
#     `address` text COLLATE utf8_unicode_ci NOT NULL,
#     `destination` text COLLATE utf8_unicode_ci NOT NULL
#   ) ENGINE=MyISAM DEFAULT CHARSET=utf8 COLLATE=utf8_unicode_ci
#   CREATE TABLE `mail_domains` (
#     `domain` text COLLATE utf8_unicode_ci NOT NULL
#   ) ENGINE=MyISAM DEFAULT CHARSET=utf8 COLLATE=utf8_unicode_ci
#   CREATE TABLE `mail_users` (
#     `address` text COLLATE utf8_unicode_ci NOT NULL,
#     `password` varchar(64) COLLATE utf8_unicode_ci NOT NULL,
#     `maildir` text COLLATE utf8_unicode_ci NOT NULL,
#     PRIMARY KEY (`address`(50))
#   ) ENGINE=MyISAM DEFAULT CHARSET=utf8 COLLATE=utf8_unicode_ci
#  The password should be crypted via MySQL's MD5() function.
#
# Parameters:
#  certs: Where to search for the certificates to use for SSL/TLS. This should be in the form of a puppet resource. The secret key will be searched via a file source parameter, using
#         'puppet:///$certs.key' as the value. The signed certificate is searched as a template via template('$certs.pem').
#  deploycerts: Whether to roll out the certs. Defaults to true, but you want to disable it if you use generic certs for this, that have been rolled out via other means.
#  postmaster: The email address for the maintainer of this server. In most cases, this probably should be 'support@kumina.nl', so we default to that.
#  monitor_username: The username setup for monitoring checks.
#  monitor_password: The password used for the monitor_username to perform connection checks.
#  mysql_user: The user to use to connect with MySQL for account information. Defaults to 'mailserver'.
#  mysql_pass: The password to use to connect with MySQL for account information.
#  mysql_db: The database/schema to connect to within MySQL. Defaults to 'mailserver'.
#  mysql_host: The MySQL host to connect to, defaults to 'localhost'. If this value is 'localhost' or '127.0.0.1', most of the MySQL setup will be done as well. You still need to create the tables
#              manually, though. If the MySQL server is not running locally, the credentials get exported.
#  mysql_tag: The tag to use when exporting the MySQL credentials. Defaults to false, to use the default tag.
#
# Depends:
#  kbp_ssl
#  kbp_ferm
#  kbp_icinga
#  kbp_mysql
#  gen_dovecot
#  gen_puppet
#
class kbp_dovecot::imap($certs, $monitor_username=false, $monitor_password=false, $deploycerts=true, $postmaster='support@kumina.nl', $mysql_user='mailserver', $mysql_pass, $mysql_db='mailserver', $mysql_host='localhost', $mysql_tag=false) {
  include gen_dovecot::imap
  include gen_dovecot::sieve
  include gen_dovecot::mysql

  $key_name = regsubst($certs,'^(.*)/(.*)$','\2')

  file {
    "/srv/mail":
      ensure  => directory,
      owner   => "mail",
      group   => "mail",
      mode    => 700;
    "/srv/sieve":
      ensure  => directory,
      owner   => "mail",
      group   => "mail",
      mode    => 700;
    "/etc/dovecot/dovecot-sql.conf":
      content => template("kbp_dovecot/dovecot-sql.conf"),
      mode    => 600,
      require => Package["dovecot-common"];
  }

  if $lsbdistcodename == 'wheezy' {
    file { "/etc/dovecot/dovecot.conf":
      content => template("kbp_dovecot/dovecot.conf.wheezy"),
      notify  => Service["dovecot"],
      require => Package["dovecot-common"];
    }
  } else {
    file { "/etc/dovecot/dovecot.conf":
      content => template("kbp_dovecot/dovecot.conf"),
      notify  => Service["dovecot"],
      require => Package["dovecot-common"];
    }
  }

  if $deploycerts {
    kbp_ssl::keys { $certs:; }
  }

  kbp_ferm::rule {
    "Sieve connections":
      proto  => "tcp",
      dport  => "4190",
      action => "ACCEPT";
    "IMAP connections":
      proto  => "tcp",
      dport  => "(143 993)",
      action => "ACCEPT";
  }

  kbp_icinga::service {
    "${servername} IMAPS":
      service_description => "IMAPS",
      check_command       => "check_imaps",
      check_interval      => 300;
  }

  if $monitor_username {
    kbp_icinga::service {
      "${servername} IMAP login":
        service_description => "IMAP login",
        check_command       => "check_imap_login",
        arguments           => [$monitor_username, $monitor_password],
        check_interval      => 300;
    }
  }

  if $mysql_host == false or $mysql_host == 'localhost' or $mysql_host == '127.0.0.1' {
    # Setup the database credentials if it's running on this host.
    if !defined(Class["kbp_mysql::server"]) {
      include kbp_mysql::server
    }

    file {
      '/var/tmp/mailserver-tables.sql':
        content => template('kbp_dovecot/mailserver-tables.sql');
    }

    mysql::server::grant { "${mysql_user} on ${mysql_db}":
      hostname => '127.0.0.1',
      password => $mysql_pass,
      notify   => Exec['create-mailserver-tables'];
    }

    exec { 'create-mailserver-tables':
      refreshonly => true,
      command     => "/usr/bin/mysql -h 127.0.0.1 -u ${mysql_user} -p${mysql_pass} ${mysql_db} < /var/tmp/mailserver-tables.sql",
      require     => [File['/var/tmp/mailserver-tables.sql'], Mysql::Server::Grant["${mysql_user} on ${mysql_db}"]];
    }
  } else {
    # Create the actual tag.
    $real_mysql_tag = $mysql_tag ? {
      false   => "mysql_${environment}_${custenv}",
      default => "mysql_${environment}_${custenv}_${mysql_tag}",
    }

    # Export the database credentials.
    @@mysql::server::grant { "${mysql_user} on ${mysql_db} for ${fqdn}":
      hostname => $fqdn,
      password => $mysql_pass,
      tag      => $real_mysql_tag;
    }
  }
}
