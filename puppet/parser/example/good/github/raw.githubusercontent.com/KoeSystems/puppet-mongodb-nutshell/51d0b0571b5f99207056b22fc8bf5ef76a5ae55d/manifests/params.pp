# == Class: mongodb::params
#
# MongoDB "static" params
#
# === Parameters
#
# Document parameters here.
#
# [*run_as_user*]
#   Name of the user and groud that will be created to run mongoDB
#
# [*service_name*]
#   Service name for the mongoDB daemon process
#
# [*version**]
#    MongoDB version
#
# [*mongodb_path*]
#   MongoDB nutshell path, all the subdirectories will use this path
#
# [*mongodb_dir_logs*]
#   Path for mongoDB logs
#
# [*mongodb_dir_etc*]
#   Path for mongoDB configuration files
#
# [*mongodb_dir_data*]
#   Path for mongoDB data storage
#
# [*ulimit_nofiles*]
#   Number of max open files
#
# === Authors
#
# Koe <koe.systems@gmail.com>
#
# === Copyright
#
# Copyright 2013 Koe

class mongodb::params {
    $run_as_user      = 'mongodb'
    $service_name     = 'mongodb'
    $version          = '2.4.6'
    $mongodb_path     = '/opt/mongodb'
    $mongodb_dir_logs = "${mongodb_path}/logs"
    $mongodb_dir_etc  = "${mongodb_path}/etc"
    $mongodb_dir_data = "${mongodb_path}/data"
    $ulimit_nofiles   = '64000'
}
