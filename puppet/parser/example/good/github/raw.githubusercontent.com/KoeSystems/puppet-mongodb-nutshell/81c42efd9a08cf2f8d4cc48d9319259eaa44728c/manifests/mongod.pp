# == Class: mongodb::mongod
#
# Configure one mongod instance using the mongoDB in a nutshell instalation
#
# === Parameters
#
# Document parameters here.
#
# [*mongod_instance*]
#   MongoDB instance name
#
# [*mongod_bind_ip*]
#   The IP address that the mongod process will bind to and listen for connections
#
# [*mongod_port*]
#   Specifies a TCP port for the mongod to listen for client connections.
#
# [*mongod_fork*]
#   Enables a daemon mode for mongod that runs the process to the background.
#
# [*mongod_pidfilepath*]
#   Specify a file location to hold the PID or process ID of the mongod process.
#
# [*mongod_directoryperdb*]
#   Specify a directory for the mongod instance to store its data.
#
# [*mongod_objcheck*]
#   Validate all the request from clients upon receipt to ensure that clients never insert invalid documents.
#
# [*mongod_journal*]
#   Enables operation journaling to ensure write durability and data consistency.
#
# [*mongod_jornulCommitInterval*]
#   Specifies the maximum amount of time for mongod to allow between journal operations.
#
# [*mongod_nssize*]
#   Specifies the default size for namespace files. Each collection, as well as each index, counts as a namespace.
#
# [*mongod_maxconn*]
#   Specifies the maximum number of simultaneous connections that mongod will accept.
#
# [*mongod_oplogSize*]
#   Specifies a maximum size in megabytes for the replication operation log.
#
# [*mongod_replSet*]
#   Use this option to configure replication with replica sets. All hosts must have the same set name.
#
# [*mongod_shardsvr*]
#   Configures this mongod instance as a shard in a partitioned cluster.
#
# [*mongod_logappend*]
#   When specified, this option ensures that mongod appends new entries to the end of the logfile rather than overwriting the content of the log when the process restarts.
#
# [*mongod_profile*]
#   Changes the level of database profiling.
#
# [*mongod_diaglog*]
#   Creates a very verbose, diagnostic log for troubleshooting and recording various errors.
#
# [*mongod_rest*]
#   Enables the simple REST API.
#
# [*mongod_nohttpinterface*]
#   Disables the http interface
#
# [*mongod_noscripting*]
#   Disables the scripting in server side
#
# [*mongod_auth*]
#   Enables database authentication for users connecting from remote hosts.
#
# [*mongod_usekey*]
#   Specify the path to a key file to store authentication information.
#
# === Authors
#
# Koe <koe.systems@gmail.com>
#
# === Copyright
#
# Copyright 2013 Koe

define mongodb::mongod (
    $mongod_instance              = $name,
    $mongod_bind_ip               = '',
    $mongod_port                  = '27017',
    $mongod_fork                  = true,
    $mongod_pidfilepath           = "${mongodb::params::mongodb_dir_data}",
    $mongod_directoryperdb        = true,
    $mongod_journal               = true,
    $mongod_journalCommitInterval = '100',
    $mongod_nssize                = '2047',
    $mongod_maxconn               = '',
    $mongod_objcheck              = true,
    $mongod_oplogSize             = '2048',
    $mongod_replSet               = '',
    $mongod_shardsvr              = false,
    $mongod_logappend             = false,
    $mongod_profile               = '0',
    $mongod_diaglog               = '0',
    $mongod_rest                  = false,
    $mongod_nohttpinterface       = true,
    $mongod_noscripting           = false,
    $mongod_auth                  = false,
    $mongod_usekey                = false,
) {

    File {
      owner   => "${mongodb::params::run_as_user}",
      group   => "${mongodb::params::run_as_user}",
    }

    file { "${mongodb::params::mongodb_dir_etc}/${mongod_instance}.conf":
      content => template('mongodb/mongod.conf.erb'),
      mode    => '0640',
      require => Class['mongodb::install']
    }

    file { "/etc/init.d/${mongod_instance}":
      content => template('mongodb/init.d.mongod.erb'),
      owner   => 'root',
      group   => 'root',
      mode    => '0750',
      require => Class['mongodb::install'],
    }

    # Create mongod data path
    file { "${mongodb::params::mongodb_dir_data}/${mongod_instance}":
        ensure  => 'directory',
        mode    => '0750'
    }

    if ($mongod_usekey != false){
      file { "${mongodb::params::mongodb_dir_etc}/${mongod_instance}.key":
        content => template('mongodb/mongod.key.erb'),
        mode    => '0600',
        require => Class['mongodb::install'],
      }
    }
}
