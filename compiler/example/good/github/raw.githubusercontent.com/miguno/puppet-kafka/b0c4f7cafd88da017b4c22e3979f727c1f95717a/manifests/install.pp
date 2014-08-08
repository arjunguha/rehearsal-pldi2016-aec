# == Class kafka::install
#
class kafka::install inherits kafka {

  package { 'kafka':
    ensure  => $package_ensure,
    name    => $package_name,
  }

  # We primarily (or only?) create this directory because some Kafka scripts have hard-coded references to it.
  file { $embedded_log_dir:
    ensure  => directory,
    owner   => $kafka::user,
    group   => $kafka::group,
    mode    => '0755',
    require => Package['kafka'],
  }

  file { $system_log_dir:
    ensure  => directory,
    owner   => $kafka::user,
    group   => $kafka::group,
    mode    => '0755',
  }

  if $limits_manage == true {
    limits::fragment {
      "${user}/soft/nofile": value => $limits_nofile;
      "${user}/hard/nofile": value => $limits_nofile;
    }
  }

  if $tmpfs_manage == false {
    # These 'log' directories are used to store the actual data being sent to Kafka.  Do not confuse them with logging
    # directories such as /var/log/*.
    kafka::install::create_log_dirs { $log_dirs: }
  }
  else {
    # We must first create the directory that we intend to mount tmpfs on.
    file { $tmpfs_path:
      ensure => directory,
      owner  => $kafka::user,
      group  => $kafka::group,
      mode   => '0750',
    }->
    mount { $tmpfs_path:
      ensure  => mounted,
      device  => 'none',
      fstype  => 'tmpfs',
      atboot  => true,
      options => "size=${tmpfs_size}",
    }->
    kafka::install::create_log_dirs { $log_dirs: }
  }

}
