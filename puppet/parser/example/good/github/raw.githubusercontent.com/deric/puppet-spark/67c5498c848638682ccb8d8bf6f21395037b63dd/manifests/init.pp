# == Class: spark
#
# Full description of class spark here.
#
# === Parameters
#
# Document parameters here.
#
# [*sample_parameter*]
#   Explanation of what this parameter affects and what it defaults to.
#   e.g. "Specify one or more upstream ntp servers as an array."
#
# === Variables
#
# Here you should define a list of variables that this module would require.
#
# [*sample_variable*]
#   Explanation of how this variable affects the funtion of this class and if it
#   has a default. e.g. "The parameter enc_ntp_servers must be set by the
#   External Node Classifier as a comma separated list of hostnames." (Note,
#   global variables should not be used in preference to class parameters  as of
#   Puppet 2.6.)
#
# === Examples
#
#  class { spark: }
#
# === Authors
#
# Tomas Barton <barton.tomas@gmail.com>
#
# === Copyright
#
# Copyright 2013-2014 Tomas Barton
#
class spark(
  $mesos_master  = 'localhost:5050',
  $package       = 'apache-spark',
  $version       = 'present',
  $home          = '/tmp/spark',
  $scala_version = '2.9.3-400',
  $scala_home    = '/usr',
  $scala_lib     = '/usr/share/java',
  $mesos_lib     = '/usr/local/lib/libmesos.so',
  $executor_uri  = '/usr/share/spark',
  $local_ip      = $::ipaddress,
  ) {

  anchor { 'spark::start': }->
  class { 'spark::install':
    package => $package,
    ensure  => $version,
  }->
  class { 'spark::config':
    scala_version => $scala_version,
    scala_home    => $scala_home,
    scala_lib     => $scala_lib,
    mesos_master  => $mesos_master,
    mesos_lib     => $mesos_lib,
    executor_uri  => $executor_uri,
    local_ip      => $local_ip,
  }->
  anchor { 'spark::end': }

}
