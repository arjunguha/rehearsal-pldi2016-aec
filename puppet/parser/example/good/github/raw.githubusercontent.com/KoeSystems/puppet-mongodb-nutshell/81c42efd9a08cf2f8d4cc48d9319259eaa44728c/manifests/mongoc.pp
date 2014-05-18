# == Class: mongodb::mongoc
#
# Configure one mongod instance like config server (sharding environment) using the mongoDB in a nutshell instalation
#
# === Parameters
#
# Document parameters here.
#
# [*mongoc_instance*]
#   MongoDB instance name
#
# [*mongoc_bind_ip*]
#   The IP address that the mongod process will bind to and listen for connections
#
# [*mongoc_port*]
#   Specifies a TCP port for the mongod to listen for client connections.
#
# [*mongoc_fork*]
#   Enables a daemon mode for mongod that runs the process to the background.
#
# [*mongoc_pidfilepath*]
#   Specify a file location to hold the PID or process ID of the mongoc process.
#
# [*mongoc_directoryperdb*]
#   Specify a directory for the mongod instance to store its data.
#
# [*mongoc_objcheck*]
#   Validate all the request from clients upon receipt to ensure that clients never insert invalid documents.
#
# [*mongoc_journal*]
#   Enables operation journaling to ensure write durability and data consistency.
#
# [*mongoc_journalCommitInterval*]
#   Specifies the maximum amount of time for mongoc to allow between journal operations.
#
# [*mongoc_nssize*]
#   Specifies the default size for namespace files. Each collection, as well as each index, counts as a namespace.
#
# [*mongoc_maxconn*]
#   Specifies the maximum number of simultaneous connections that mongos will accept.
#
# [*mongoc_oplogSize*]
#   Specifies a maximum size in megabytes for the replication operation log.
#
# [*mongoc_configsvr*]
#   Declares that this mongod instance serves as the config database of a sharded cluster.
#
# [*mongoc_logappend*]
#   When specified, this option ensures that mongod appends new entries to the end of the logfile rather than overwriting the content of the log when the process restarts.
#
# [*mongoc_profile*]
#   Changes the level of database profiling.
#
# [*mongoc_diaglog*]
#   Creates a very verbose, diagnostic log for troubleshooting and recording various errors.
#
# [*mongoc_rest*]
#   Enables the simple REST API.
#
# [*mongoc_nohttpinterface*]
#   Disables the http interface
#
# [*mongoc_noscripting*]
#   Disables the scripting in server side
#
# [*mongoc_auth*]
#   Enables database authentication for users connecting from remote hosts.
#
# [*mongoc_usekey*]
#   Specify the path to a key file to store authentication information.
#
# === Authors
#
# Koe <koe.systems@gmail.com>
#
# === Copyright
#
# Copyright 2013 Koe

define mongodb::mongoc (
    $mongoc_instance              = $name,
    $mongoc_bind_ip               = '',
    $mongoc_port                  = '27019',
    $mongoc_fork                  = true,
    $mongoc_pidfilepath           = "${mongodb::params::mongodb_dir_data}",
    $mongoc_directoryperdb        = true,
    $mongoc_journal               = true,
    $mongoc_journalCommitInterval = '100',
    $mongoc_nssize                = '2047',
    $mongoc_maxconn               = '',
    $mongoc_objcheck              = true,
    $mongoc_oplogSize             = '2048',
    $mongoc_logappend             = false,
    $mongoc_profile               = '0',
    $mongoc_diaglog               = '0',
    $mongoc_rest                  = false,
    $mongoc_nohttpinterface       = true,
    $mongoc_noscripting           = false,
    $mongoc_auth                  = false,
    $mongoc_usekey                = false,
) {

    File {
      owner   => "${mongodb::params::run_as_user}",
      group   => "${mongodb::params::run_as_user}",
    }

    file { "${mongodb::params::mongodb_dir_etc}/${mongoc_instance}.conf":
      content => template('mongodb/mongoc.conf.erb'),
      mode    => '0640',
      require => Class['mongodb::install']
    }

    file { "/etc/init.d/${mongoc_instance}":
      content => template('mongodb/init.d.mongoc.erb'),
      owner   => 'root',
      group   => 'root',
      mode    => '0750',
      require => Class['mongodb::install'],
    }

    # Create mongoc data path
    file { "${mongodb::params::mongodb_dir_data}/${mongoc_instance}":
        ensure  => 'directory',
        mode    => '0750'
    }

    if ($mongoc_usekey != false){
      file { "${mongodb::params::mongodb_dir_etc}/${mongoc_instance}.key":
        content => template('mongodb/mongoc.key.erb'),
        mode    => '0600',
        require => Class['mongodb::install'],
      }
    }
}
