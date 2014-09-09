# == Class: mongodb::install
#
# Class to install mongoDB in a nutshell. Inherits the param subclass with the "static" configuration.
#
# === Authors
#
# Koe <koe.systems@gmail.com>
#
# === Copyright
#
# Copyright 2013 Koe
#

class mongodb::install inherits mongodb::params {

    # Create mongo user and group
    group { "${run_as_user}":
        ensure => 'present'
    }

    user { "${run_as_user}":
        ensure       =>  'present',
        system       =>  true,
        groups       =>  "${run_as_user}",
        shell        =>  '/bin/false',
        home         =>  "${mongodb_path}",
        managehome   =>  true,
        require      =>  Group["${run_as_user}"]
    }

    # Create mongoDB paths for bin, logs, config and data
    file { ["${mongodb_path}","${mongodb_path}/bin","${mongodb_dir_logs}","${mongodb_dir_etc}","${mongodb_dir_data}"]:
        ensure  => 'directory',
        owner   => "${run_as_user}",
        group   => "${run_as_user}",
        mode    => '0750',
        require => User["${run_as_user}"]
    }

    # Install mongoDB 32bits or 64bits binaries
    case $::architecture {
      amd64: {

        # Upload the tar file from puppet master
        file { "/tmp/mongodb-linux-x86_64-${version}.tgz":
          ensure  => 'present',
          source  => "puppet:///modules/mongodb/mongodb-linux-x86_64-${version}.tgz",
          require => User["${run_as_user}"],
        }

        # Untar mongoDB
        exec { "tar xvf /tmp/mongodb-linux-x86_64-${version}.tgz --strip 1 mongodb-linux-x86_64-${version}/bin":
          path     => [ '/bin/', '/sbin/' , '/usr/bin/', '/usr/sbin/' ],
          cwd      => "${mongodb_path}",
          creates  => "${mongodb_path}/bin/mongod",
          alias    => 'untar-mongodb-linux',
          require  => File["/tmp/mongodb-linux-x86_64-${version}.tgz"]
        }
      }
      x86: {

        # Upload the tar file from puppet master
        file { "/tmp/mongodb-linux-i686-${version}.tgz":
          ensure  => 'present',
          source  => "puppet:///modules/mongodb/mongodb-linux-i686-${version}.tgz",
          require =>  User["${run_as_user}"],
        }

        # Untar mongoDB
        exec { "tar xvf /tmp/mongodb-linux-i686-${version}.tgz --strip 1 mongodb-linux-i686-${version}/bin":
          path     => [ '/bin/', '/sbin/' , '/usr/bin/', '/usr/sbin/' ],
          cwd      => "${mongodb_path}",
          creates  => "${mongodb_path}/bin/mongod",
          alias    => 'untar-mongodb-linux',
          require  => File["/tmp/mongodb-linux-i686-${version}.tgz"]
        }
      }
      default: {
        fail('Only linux OS supported')
      }
    }
}
