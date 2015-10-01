# From https://github.com/antonlindstrom/puppet-powerdns
# Replaced usage of selector syntax with if expressions.

# Public: Set confguration directives in a .d directory
#
# name   - Name of the configuration directive, for example cache-ttl
# value  - Value of the config, for cache-ttl it could be 20
# ensure - Ensure it to be either present or absent
#
# Example:
#
#    powerdns::config { 'cache-ttl':
#      ensure => present,
#      value  => 20,
#    }
#
define powerdns::config(
  $value,
  $ensure = 'present',
) {

  file { "${name}.conf":
    ensure  => $ensure,
    path    => "${powerdns::params::cfg_include_path}/${name}.conf",
    owner   => 'root',
    group   => 'root',
    mode    => '0600',
    content => "${name}=${value}\n",
    require => Class['powerdns::package'],
    notify  => Class['powerdns::service'],
  }

}
# Public: Install the powerdns server
#
# ensure - Ensure powerdns to be present or absent
# source - Source package of powerdns server,
#          default is package provider
#
# Example:
#
#    # Include with default
#    include powerdns
#
class powerdns(
  $ensure = 'present',
  $source = ''
) {

  anchor { 'powerdns::begin': ;
    'powerdns::end':
  }

  class { 'powerdns::package':
    ensure => $ensure,
    source => $source
  }

  class { 'powerdns::service':
    ensure => $ensure,
  }

  Anchor['powerdns::begin'] -> Class['powerdns::service'] -> Anchor['powerdns::end']
  Anchor['powerdns::begin'] -> Class['powerdns::package'] -> Anchor['powerdns::end']
}
# Public: Install the powerdns ldap backend
#
# package  - which package to install
# ensure   - ensure postgres backend to be present or absent
# source   - where to get the package from
# ldap_host   - host to connect to
# ldap_basedn - which base in the ldap we must be searched in
# ldap_binddn - which user powerdns should connect as
# ldap_secret - which password to use with user
#
class powerdns::ldap(
  $package     = $powerdns::params::package_ldap,
  $ensure      = 'present',
  $source      = '',
  $ldap_host   = '',
  $ldap_basedn = '',
  $ldap_binddn = '',
  $ldap_secret = '',
) inherits powerdns::params {

  require ::powerdns::package

  $package_source = if $source == '' {
    undef
  } else {
    $source
  }

  $package_provider = if $source == '' {
    undef
  } else {
    $powerdns::params::package_provider
  }

  package { $package:
    ensure   => $ensure,
    require  => Package[$powerdns::params::package],
    provider => $package_provider,
    source   => $package_source
  }

  file { $powerdns::params::ldap_cfg_path:
    ensure  => $ensure,
    owner   => root,
    group   => root,
    mode    => '0600',
    content => template('powerdns/pdns.ldap.local.erb'),
    notify  => Service['pdns'],
    require => Package[$package],
  }
}

# Public: Install the powerdns mysql backend
#
# package  - which package to install
# ensure   - ensure postgres backend to be present or absent
# source   - where to get the package from
# user     - which user powerdns should connect as
# password - which password to use with user
# host     - host to connect to
# port     - port to connect to
# dbname   - which database to use
# dnssec   - enable or disable dnssec either yes or no
#
class powerdns::mysql(
  $package  = $powerdns::params::package_mysql,
  $ensure   = 'present',
  $source   = '',
  $user     = '',
  $password = '',
  $host     = 'localhost',
  $port     = '3306',
  $dbname   = 'pdns',
  $dnssec   = 'yes'
) inherits powerdns::params {

  $package_source = if $source == '' {
    undef
  } else {
    $source
  }

  $package_provider = if $source == '' {
    undef
  } else {
    $powerdns::params::package_provider
  }

  package { $package:
    ensure   => $ensure,
    require  => Package[$powerdns::params::package],
    provider => $package_provider,
    source   => $package_source
  }

  file { $powerdns::params::mysql_cfg_path:
    ensure  => $ensure,
    owner   => root,
    group   => root,
    mode    => '0600',
    backup  => '.bak',
    content => template('powerdns/pdns.mysql.local.erb'),
    notify  => Service['pdns'],
    require => Package[$powerdns::params::package],
  }
}
# Internal: Install the powerdns package
#
# Example:
#
#    include powerdns::package
#
class powerdns::package(
  $package = $powerdns::params::package,
  $ensure = 'present',
  $source = ''
) inherits powerdns::params {

  $package_source = if $source == '' {
    undef
  } else {
    $source
  }

  $package_provider = if $source == '' {
    undef
  } else {
    $powerdns::params::package_provider
  }

  package { $package:
    ensure   => $ensure,
    source   => $package_source,
    provider => $package_provider
  }

  file { $powerdns::params::cfg_include_path :
    ensure  => directory,
    owner   => 'root',
    group   => 'root',
    mode    => '0755',
    require => Package[$package],
  }

}
# Internal: Set default parameters
#
# Example:
#
#    include powerdns::params
#
class powerdns::params {

  $package = if $::operatingsystem =~ /(?i:centos|redhat|amazon)/ {
    'pdns'
  } else {
    'pdns-server'
  }

  $package_provider = if $::operatingsystem =~ /(?i:centos|redhat|amazon)/ {
    'rpm'
  } else {
    'dpkg'
  }

  $package_psql = if $::operatingsystem =~ /(?i:centos|redhat|amazon)/ {
    'pdns-backend-postgresql'
  } else {
    'pdns-backend-pgsql'
  }

  $package_mysql = if $::operatingsystem =~ /(?i:centos|redhat|amazon)/ {
    'pdns-backend-mysql'
  } else {
    'pdns-backend-mysql'
  }

  $package_ldap = if $::operatingsystem =~ /(?i:centos|redhat|amazon)/ {
    'pdns-backend-ldap'
  } else {
    'pdns-backend-ldap'
  }

  $package_recursor = if $::operatingsystem =~ /(?i:centos|redhat|amazon)/ {
    'pdns-recursor'
  } else {
    'pdns-recursor'
  }

  $postgresql_cfg_path = if $::operatingsystem =~ /(?i:centos|redhat|amazon)/ {
    '/etc/pdns/pdns.conf'
  } else {
    '/etc/powerdns/pdns.d/pdns.local.gpgsql.conf'
  }

  $mysql_cfg_path = if $::operatingsystem =~ /(?i:centos|redhat|amazon)/ {
    '/etc/pdns/pdns.conf'
  } else {
    '/etc/powerdns/pdns.d/pdns.local.gmysql.conf'
  }

  $ldap_cfg_path = if $::operatingsystem =~ /(?i:centos|redhat|amazon)/ {
    '/etc/pdns/pdns.conf'
  } else {
    '/etc/powerdns/pdns.d/pdns.local.ldap.conf'
  }

  $recursor_cfg_path = if $::operatingsystem =~ /(?i:centos|redhat|amazon)/ {
    '/etc/pdns/recursor.conf'
  } else {
    '/etc/powerdns/recursor.conf'
  }

  $cfg_include_name = if $::operatingsystem =~ /(?i:centos|redhat|amazon)/ {
    'include-dir'
  } else {
    'include'
  }

  $cfg_include_path = if $::operatingsystem =~ /(?i:centos|redhat|amazon)/ {
    '/etc/pdns/conf.d'
  } else {
    '/etc/powerdns/pdns.d'
  }
}
# Public: Install the powerdns postgresql backend
#
# package  - which package to install
# ensure   - ensure postgres backend to be present or absent
# source   - where to get the package from
# user     - which user powerdns should connect as
# password - which password to use with user
# host     - host to connect to
# port     - port to connect to
# dbname   - which database to use
# dnssec   - enable or disable dnssec either yes or no
#
class powerdns::postgresql(
  $package  = $powerdns::params::package_psql,
  $ensure   = 'present',
  $source   = '',
  $user     = '',
  $password = '',
  $host     = 'localhost',
  $port     = '5432',
  $dbname   = 'pdns',
  $dnssec   = 'yes'
) inherits powerdns::params {

  $postgres_schema = if $dnssec =~ /(yes|true)/ {
    'puppet:///modules/powerdns/postgresql_schema.dnssec.sql'
  } else {
    'puppet:///modules/powerdns/postgresql_schema.sql'
  }

  $package_source = if $source == '' {
    undef
  } else {
    $source
  }

  $package_provider = if $source == '' {
    undef
  } else {
    $powerdns::params::package_provider
  }

  package { $package:
    ensure   => $ensure,
    require  => Package[$powerdns::params::package],
    provider => $package_provider,
    source   => $package_source
  }

  file { $powerdns::params::postgresql_cfg_path:
    ensure  => $ensure,
    owner   => root,
    group   => root,
    mode    => '0600',
    backup  => '.bak',
    content => template('powerdns/pdns.pgsql.local.erb'),
    notify  => Service['pdns'],
    require => Package[$powerdns::params::package],
  }

  file { '/opt/powerdns_schema.sql':
    ensure => $ensure,
    owner  => root,
    group  => root,
    mode   => '0644',
    source => $postgres_schema
  }

}
# Public: Install the powerdns-recursor server
#
# package - Name of the package to install
# ensure  - Ensure powerdns to be present or absent
# source  - Source package of powerdns server,
#           default is package provider
#
# configs used into the template:
#   forward_zones
#   forward_zones_recurse
#   local_address
#   local_port
#   log_common_errors
#   logging_facility
#   max_negative_ttl
#   quiet
#   setgid
#   setuid
#   trace
#
# Example:
#
#    # Include with default
#    include powerdns::recursor
#
class powerdns::recursor(
  $package               = $powerdns::params::package_recursor,
  $ensure                = 'present',
  $source                = '',
  $forward_zones         = undef,
  $forward_zones_recurse = undef,
  $local_address         = '127.0.0.1',
  $local_port            = '53',
  $log_common_errors     = 'yes',
  $logging_facility      = undef,
  $max_negative_ttl      = undef,
  $quiet                 = 'yes',
  $setgid                = 'pdns',
  $setuid                = 'pdns',
  $trace                 = 'off',

) inherits powerdns::params {

  require ::powerdns

  $package_source = if $source == '' {
    undef
  } else {
    $source
  }

  $package_provider = if $source == '' {
    undef
  } else {
    $powerdns::params::package_provider
  }

  package { $package:
    ensure   => $ensure,
    require  => Package[$powerdns::params::package],
    provider => $package_provider,
    source   => $package_source
  }

  file { $powerdns::params::recursor_cfg_path:
    ensure  => $ensure,
    owner   => root,
    group   => root,
    mode    => '0600',
    content => template('powerdns/recursor.conf.erb'),
    notify  => Service['pdns-recursor'],
    require => Package[$package],
  }

  $ensure_service = if $ensure == 'present' {
    'running'
  } else {
    'stopped'
  }

  service { 'pdns-recursor':
    ensure     => $ensure_service,
    enable     => true,
    hasrestart => true,
    hasstatus  => true,
    require    => Package[$package],
  }
}

# Internal: Ensure the service to be either started or stopped
#
# Example:
#
#    include powerdns::service
#
class powerdns::service(
  $ensure = 'present'
) {

  $ensure_service = if $ensure == 'present' {
    'running'
  } else {
    'stopped'
  }

  service { 'pdns':
    ensure     => $ensure_service,
    enable     => true,
    hasrestart => true,
    hasstatus  => true,
    require    => Class['powerdns::package']
  }

}
