# == Class: kafka
#
# Deploys an Apache Kafka broker.
#
# === Parameters
#
# TODO: Document each class parameter.
#
# [*kafka_gc_log_opts*]
#   Use this parameter for all Java Garbage Collection settings with the exception of configuring `-Xloggc:...`.
#   Use $gc_log_file for the latter.
#
# [*kafka_log4j_opts*]
#   Use this parameter for all logging settings with the exception of configuring `-Dlog4j.configuration.file=...`.
#   Use $logging_config for the latter.
#
# [*log_dirs*]
#   An array of (absolute) paths that Kafka will use to store its data log files.  Note that the term "log file" here
#   is not referring to logging data such as `/var/log/*`.  Using `$tmpfs_manage` you have the option to place one or
#   more log directories on tmpfs, although you will lose any durability/persistence of course when doing so.
#   Typically, you will not use tmpfs for Kafka's log directories.  Default: ['/app/kafka/log']
#
# [*tmpfs_manage*]
#   If true we create a tmpfs mount (see `$tmpfs_path`), which can be used to host Kafka's log directories (see
#   `$log_dirs`.  Default: false.
#
# [*tmpfs_path*]
#   The path to mount tmpfs.  At the moment the path must be a top-level directory (e.g. `/foo` is ok, but `/foo/bar`
#   is not).  Any `$log_dirs` that you want to place on tmpfs should be sub-directories of `$tmpfs_path`.  For instance,
#   if `$tmpfs_path` is set to `/tmpfs`, then you may want to use [`/tmpfs/dir1`, `/tmpfs/dir2`] for `$log_dirs`.
#   Default: `/tmpfs`.
#
# [*tmpfs_size*]
#   The size of the tmpfs mount.  Default: 0k.
#
# Note: When using a custom namespace/chroot in the ZooKeeper connection string you must manually create the namespace
#       in ZK first (e.g. in 'localhost:2181/kafka' the namespace is '/kafka').
#
class kafka (
  $base_dir            = $kafka::params::base_dir,
  $broker_id           = $kafka::params::broker_id,
  $broker_port         = $kafka::params::broker_port,
  $command             = $kafka::params::command,
  $config              = $kafka::params::config,
  $config_map          = $kafka::params::config_map,
  $config_template     = $kafka::params::config_template,
  $embedded_log_dir    = $kafka::params::embedded_log_dir,
  $gc_log_file         = $kafka::params::gc_log_file,
  $gid                 = $kafka::params::gid,
  $group               = $kafka::params::group,
  $group_ensure        = $kafka::params::group_ensure,
  $hostname            = $kafka::params::hostname,
  $jmx_port            = $kafka::params::jmx_port,
  $kafka_gc_log_opts   = $kafka::params::kafka_gc_log_opts,
  $kafka_heap_opts     = $kafka::params::kafka_heap_opts,
  $kafka_jmx_opts      = $kafka::params::kafka_jmx_opts,
  $kafka_jvm_performance_opts = $kafka::params::kafka_jvm_performance_opts,
  $kafka_log4j_opts    = $kafka::params::kafka_log4j_opts,
  $kafka_opts          = $kafka::params::kafka_opts,
  $limits_manage       = hiera('kafka::limits_manage', $kafka::params::limits_manage),
  $limits_nofile       = $kafka::params::limits_nofile,
  $log_dirs            = $kafka::params::log_dirs,
  $logging_config      = $kafka::params::logging_config,
  $logging_config_template        = $kafka::params::logging_config_template,
  $package_ensure      = $kafka::params::package_ensure,
  $package_name        = $kafka::params::package_name,
  $service_autorestart = hiera('kafka::service_autorestart', $kafka::params::service_autorestart),
  $service_enable      = hiera('kafka::service_enable', $kafka::params::service_enable),
  $service_ensure      = $kafka::params::service_ensure,
  $service_manage      = hiera('kafka::service_manage', $kafka::params::service_manage),
  $service_name        = $kafka::params::service_name,
  $service_retries     = $kafka::params::service_retries,
  $service_startsecs   = $kafka::params::service_startsecs,
  $service_stderr_logfile_keep    = $kafka::params::service_stderr_logfile_keep,
  $service_stderr_logfile_maxsize = $kafka::params::service_stderr_logfile_maxsize,
  $service_stdout_logfile_keep    = $kafka::params::service_stdout_logfile_keep,
  $service_stdout_logfile_maxsize = $kafka::params::service_stdout_logfile_maxsize,
  $shell               = $kafka::params::shell,
  $system_log_dir      = $kafka::params::system_log_dir,
  $tmpfs_manage        = $kafka::params::tmpfs_manage,
  $tmpfs_path          = $kafka::params::tmpfs_path,
  $tmpfs_size          = $kafka::params::tmpfs_size,
  $uid                 = $kafka::params::uid,
  $user                = $kafka::params::user,
  $user_description    = $kafka::params::user_description,
  $user_ensure         = $kafka::params::user_ensure,
  $user_home           = $kafka::params::user_home,
  $user_manage         = hiera('kafka::user_manage', $kafka::params::user_manage),
  $user_managehome     = hiera('kafka::user_managehome', $kafka::params::user_managehome),
  $zookeeper_connect   = $kafka::params::zookeeper_connect,
) inherits kafka::params {

  validate_absolute_path($base_dir)
  if !is_integer($broker_id) { fail('The $broker_id parameter must be an integer number') }
  if !is_integer($broker_port) { fail('The $broker_port parameter must be an integer number') }
  validate_string($command)
  validate_absolute_path($config)
  validate_hash($config_map)
  validate_string($config_template)
  validate_absolute_path($embedded_log_dir)
  validate_absolute_path($gc_log_file)
  if !is_integer($gid) { fail('The $gid parameter must be an integer number') }
  validate_string($group)
  validate_string($group_ensure)
  validate_string($hostname)
  if !is_integer($jmx_port) { fail('The $jmx_port parameter must be an integer number') }
  validate_string($kafka_gc_log_opts)
  validate_string($kafka_heap_opts)
  validate_string($kafka_jmx_opts)
  validate_string($kafka_jvm_performance_opts)
  validate_string($kafka_log4j_opts)
  validate_string($kafka_opts)
  validate_bool($limits_manage)
  if !is_integer($limits_nofile) { fail('The $limits_nofile parameter must be an integer number') }
  validate_array($log_dirs)
  validate_absolute_path($logging_config)
  validate_string($logging_config_template)
  validate_string($package_ensure)
  validate_string($package_name)
  validate_bool($service_autorestart)
  validate_bool($service_enable)
  validate_string($service_ensure)
  validate_bool($service_manage)
  validate_string($service_name)
  if !is_integer($service_retries) { fail('The $service_retries parameter must be an integer number') }
  if !is_integer($service_startsecs) { fail('The $service_startsecs parameter must be an integer number') }
  if !is_integer($service_stderr_logfile_keep) {
    fail('The $service_stderr_logfile_keep parameter must be an integer number')
  }
  validate_string($service_stderr_logfile_maxsize)
  if !is_integer($service_stdout_logfile_keep) {
    fail('The $service_stdout_logfile_keep parameter must be an integer number')
  }
  validate_string($service_stdout_logfile_maxsize)
  validate_absolute_path($shell)
  validate_absolute_path($system_log_dir)
  validate_bool($tmpfs_manage)
  validate_absolute_path($tmpfs_path)
  validate_string($tmpfs_size)
  if !is_integer($uid) { fail('The $uid parameter must be an integer number') }
  validate_string($user)
  validate_string($user_description)
  validate_string($user_ensure)
  validate_absolute_path($user_home)
  validate_bool($user_manage)
  validate_bool($user_managehome)
  validate_array($zookeeper_connect)

  include '::kafka::users'
  include '::kafka::install'
  include '::kafka::config'
  include '::kafka::service'

  # Anchor this as per #8040 - this ensures that classes won't float off and
  # mess everything up. You can read about this at:
  # http://docs.puppetlabs.com/puppet/2.7/reference/lang_containment.html#known-issues
  anchor { 'kafka::begin': }
  anchor { 'kafka::end': }

  Anchor['kafka::begin']
  -> Class['::kafka::users']
  -> Class['::kafka::install']
  -> Class['::kafka::config']
  ~> Class['::kafka::service']
  -> Anchor['kafka::end']
}
