# == Class: mongodb::mongos
#
# Configure one mongos instance using the mongoDB in a nutshell instalation
#
# === Parameters
#
# Document parameters here.
#
# [*mongos_instance*]
#   MongoDB instance name
#
# [*mongos_bind_ip*]
#   The IP address that the mongos process will bind to and listen for connections
#
# [*mongos_port*]
#   Specifies a TCP port for the mongos to listen for client connections.
#
# [*mongos_fork*]
#   Enables a daemon mode for mongos that runs the process to the background.
#
# [*mongos_pidfilepath*]
#   Specify a file location to hold the PID or process ID of the mongos process.
#
# [*mongos_maxconn*]
#   Specifies the maximum number of simultaneous connections that mongos will accept.
#
# [*mongos_objcheck*]
#   Validate all the request from clients upon receipt to ensure that clients never insert invalid documents.
#
# [*mongos_configdb*]
#   Specify a configuration database for the sharded cluster.
#   You must specify either 1 configuration server or 3 configuration servers, in a comma separated list.
#
# [*mongos_chunkSize*]
#   Determines the size of each chunk, in megabytes, of data distributed around the sharded cluster.
#
# [*mongos_logappend*]
#   When specified, this option ensures that mongos appends new entries to the end of the logfile rather than overwriting the content of the log when the process restarts.
#
# [*mongos_nohttpinterface*]
#   Disables the http interface
#
# [*mongos_noscripting*]
#   Disables the scripting in server side
#
# === Authors
#
# Koe <koe.systems@gmail.com>
#
# === Copyright
#
# Copyright 2013 Koe

define mongodb::mongos (
    $mongos_instance              = $name,
    $mongos_bind_ip               = '',
    $mongos_port                  = '27017',
    $mongos_fork                  = true,
    $mongos_pidfilepath           = "${mongodb::params::mongodb_dir_data}",
    $mongos_maxconn               = '',
    $mongos_objcheck              = true,
    $mongos_configdb              = '',
    $mongos_chunkSize             = '64',
    $mongos_logappend             = false,
    $mongos_nohttpinterface       = true,
    $mongos_noscripting           = false,
) {

    File {
      owner   => "${mongodb::params::run_as_user}",
      group   => "${mongodb::params::run_as_user}",
    }

    file { "${mongodb::params::mongodb_dir_etc}/${mongos_instance}.conf":
      content => template('mongodb/mongos.conf.erb'),
      mode    => '0640',
      require => Class['mongodb::install']
    }

    file { "/etc/init.d/${mongos_instance}":
      content => template('mongodb/init.d.mongos.erb'),
      owner   => 'root',
      group   => 'root',
      mode    => '0750',
      require => Class['mongodb::install'],
    }

    # Create mongos data path
    file { "${mongodb::params::mongodb_dir_data}/${mongos_instance}":
        ensure  => 'directory',
        mode    => '0750'
    }
}
