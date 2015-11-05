# From https://github.com/vamsee/puppet-solr
# Replaced selector syntax.

## config.pp

# == Class: solr::config
# This class sets up solr install
#
# === Parameters
# - The $cores to create
#
# === Actions
# - Copies a new jetty default file
# - Creates solr home directory
# - Downloads the required solr version, extracts war and copies logging jars
# - Creates solr data directory
# - Creates solr config file with cores specified
# - Links solr home directory to jetty webapps directory
#
class solr::config(
  $cores          = $solr::params::cores,
  $version        = $solr::params::solr_version,
  $mirror         = $solr::params::mirror_site,
  $jetty_home     = $solr::params::jetty_home,
  $solr_home      = $solr::params::solr_home,
  ) inherits solr::params {

  $dl_name        = "solr-${version}.tgz"
  $download_url   = "${mirror}/${version}/${dl_name}"

  #Copy the jetty config file
  file { '/etc/default/jetty':
    ensure  => file,
    source  => 'puppet:///modules/solr/jetty-default',
    require => Package['jetty'],
  }

  file { $solr_home:
    ensure  => directory,
    owner   => 'jetty',
    group   => 'jetty',
    require => Package['jetty'],
  }

  # download only if WEB-INF is not present and tgz file is not in /tmp:
  exec { 'solr-download':
    path    => [ '/bin', '/sbin' , '/usr/bin', '/usr/sbin', '/usr/local/bin' ],
    command =>  "wget ${download_url}",
    cwd     =>  '/tmp',
    creates =>  "/tmp/${dl_name}",
    onlyif  =>  "test ! -d 
${solr_home}/WEB-INF && test ! -f /tmp/${dl_name}",
    timeout =>  0,
    require => File[$solr_home],
  }

  exec { 'extract-solr':
    path    => [ '/bin', '/sbin' , '/usr/bin', '/usr/sbin', '/usr/local/bin' ],
    command =>  "tar xvf ${dl_name}",
    cwd     =>  '/tmp',
    onlyif  =>  "test -f /tmp/${dl_name} && test ! -d /tmp/solr-${version}",
    require =>  Exec['solr-download'],
  }

  # have to copy logging jars separately from solr 4.3 onwards
  exec { 'copy-solr':
    path    => [ '/bin', '/sbin' , '/usr/bin', '/usr/sbin', '/usr/local/bin' ],
    command =>  "jar xvf /tmp/solr-${version}/dist/solr-${version}.war; \
    cp /tmp/solr-${version}/example/lib/ext/*.jar WEB-INF/lib",
    cwd     =>  $solr_home,
    onlyif  =>  "test ! -d ${solr_home}/WEB-INF",
    require =>  Exec['extract-solr'],
  }

  file { '/var/lib/solr':
    ensure  => directory,
    owner   => 'jetty',
    group   => 'jetty',
    mode    => '0700',
    require => Package['jetty'],
  }

  file { "${solr_home}/solr.xml":
    ensure  => 'file',
    owner   => 'jetty',
    group   => 'jetty',
    content => template('solr/solr.xml.erb'),
    require => File['/etc/default/jetty'],
  }

  file { "${jetty_home}/webapps/solr":
    ensure  => 'link',
    target  => $solr_home,
    require => File["${solr_home}/solr.xml"],
  }

  solr::core { $cores:
    require   =>  File["${jetty_home}/webapps/solr"],
  }
}

## core.pp

# == Definition: solr::core
# This definition sets up solr config and data directories for each core
#
# === Parameters
# - The $core to create
#
# === Actions
# - Creates the solr web app directory for the core
# - Copies over the config directory for the file
# - Creates the data directory for the core
#
define solr::core(
  $core_name = $title,
) {
  include solr::params

  $solr_home  = $solr::params::solr_home

  file { "${solr_home}/${core_name}":
    ensure  => directory,
    owner   => 'jetty',
    group   => 'jetty',
    require => File[$solr_home],
  }

  #Copy its config over
  file { "${solr_home}/${core_name}/conf":
    ensure  => directory,
    owner   => 'jetty',
    group   => 'jetty',
    recurse => true,
    source  => 'puppet:///modules/solr/conf',
    require => File["${solr_home}/${core_name}"],
  }

  #Finally, create the data directory where solr stores
  #its indexes with proper directory ownership/permissions.
  file { "/var/lib/solr/${core_name}":
    ensure  => directory,
    owner   => 'jetty',
    group   => 'jetty',
    require => File["${solr_home}/${core_name}/conf"],
  }

}

## init.pp

# == Class: solr
#
# This module helps you create a multi-core solr install
# from scratch. I'm packaging a version of solr in the files
# directory for convenience. You can replace it with a newer
# version if you like.
#
# IMPORTANT: Works only with Ubuntu as of now. Other platform
# support is most welcome.
#
# === Parameters
#
# [*cores*]
#   "Specify the solr cores you want to create (optional)"
#
# === Examples
#
# Default case, which creates a single core called 'default'
#
#  include solr
#
# If you want multiple cores, you can supply them like so:
#
#  class { 'solr':
#    cores => [ 'development', 'staging', 'production' ]
#  }
#
# You can also manage/create your cores from solr web admin panel.
#
# === Authors
#
# Vamsee Kanakala <vamsee AT riseup D0T net>
#
# === Copyright
#
# Copyright 2012-2013 Vamsee Kanakala, unless otherwise noted.
#

class solr (
  $cores      = 'UNSET',
  $version    = 'UNSET',
  $mirror     = 'UNSET',
) {

  include solr::params

  $my_cores = if $cores == 'UNSET' {
    $::solr::params::cores
  } else {
    $cores
  }

  $my_version = if $version == 'UNSET' {
    $::solr::params::solr_version
  } else {
    $version
  }

  $my_mirror = if $version == 'UNSET' {
    $::solr::params::mirror_site
  } else {
    $mirror
  }

  class {'solr::install': } ->
  class {'solr::config':
    cores   => $my_cores,
    version => $my_version,
    mirror  => $my_mirror,
  } ->
  class {'solr::service': } ->
  Class['solr']

}

## install.pp

# == Class: solr::install
# This class installs the required packages for jetty
#
# === Actions
# - Installs default jdk
# - Installs jetty and extra libs
#

class solr::install {

  if ! defined(Package['default-jdk']) {
      package { 'default-jdk':
        ensure    => present,
      }
  }

  if ! defined(Package['jetty']) {
      package { 'jetty':
          ensure  => present,
          require => Package['default-jdk'],
      }
  }

  if ! defined(Package['libjetty-extra']) {
      package { 'libjetty-extra':
          ensure  => present,
          require => Package['jetty'],
      }
  }

  if ! defined(Package['wget']) {
      package { 'wget':
          ensure  => present,
      }
  }

  if ! defined(Package['curl']) {
      package { 'curl':
          ensure  => present,
      }
  }

}

## params.pp

# == Class: solr::params
# This class sets up some required parameters
#
# === Actions
# - Specifies jetty and solr home directories
# - Specifies the default core
#
class solr::params {

  $jetty_home    = '/usr/share/jetty'
  $solr_home     = '/usr/share/solr'
  $solr_version  = '4.7.2'
  $mirror_site   = 'http://www.us.apache.org/dist/lucene/solr'
  $data_dir      = '/var/lib/solr'
  $cores         = ['default']

}

## service.pp

# == Class: solr::service
# This class sets up solr service
#
# === Actions
# - Sets up jetty service
#
class solr::service {

  #restart after copying new config
  service { 'jetty':
    ensure     => running,
    hasrestart => true,
    hasstatus  => true,
    require    => Package['jetty'],
  }

}
