# Class: spark::config
#
# This module manages the spark configuration directories
#
# Parameters: None
#
# Actions: None
#
# Requires: spark::install, spark
#
# Sample Usage: include spark::config
#
class spark::config(
  $mesos_master,
  $executor_uri,
  $local_ip,
  $home          = '/usr/share/spark',
  $scala_version = '2.9.3-400',
  $scala_home    = '/usr',
  $scala_lib     = '/usr/share/java',
  $mesos_lib     = '/usr/local/lib/libmesos.so',
  ) inherits spark {

  file_line { 'etc_profile_mesos_lib':
    path => '/etc/profile',
    line => 'export MESOS_NATIVE_LIBRARY="$mesos_lib"',
  }

  file_line { 'etc_profile_scala_home':
    path => '/etc/profile',
    line => 'export SCALA_HOME="$scala_home"',
  }

  file_line { 'etc_profile_scala_lib_path':
    path => '/etc/profile',
    line => 'export SCALA_LIBRARY_PATH="$scala_lib"',
  }

  file { "${home}/conf/spark-env.sh":
    ensure => file,
    content => template("spark/spark-env.sh.erb"),
#   owner => $user,
#   group => $group,
    mode => 644,
  }

  file { "${home}/conf/log4j.properties":
    ensure => file,
    content => template("spark/log4j.properties.erb"),
#   owner => $user,
#   group => $group,
    mode => 644,
  }

}
