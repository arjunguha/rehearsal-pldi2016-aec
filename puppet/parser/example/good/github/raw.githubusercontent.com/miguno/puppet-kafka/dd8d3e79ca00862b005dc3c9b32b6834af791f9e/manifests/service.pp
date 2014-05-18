# == Class kafka::service
#
class kafka::service inherits kafka {

  if !($kafka::service_ensure in ['present', 'absent']) {
    fail('service_ensure parameter must be "present" or "absent"')
  }

  if $kafka::service_manage == true {

    $kafka_gc_log_opts_prefix = "-Xloggc:${gc_log_file}"
    if $kafka_gc_log_opts {
      $kafka_gc_log_opts_real = "KAFKA_GC_LOG_OPTS=\"${kafka_gc_log_opts_prefix} ${kafka_gc_log_opts}\""
    }
    else {
      $kafka_gc_log_opts_real = "KAFKA_GC_LOG_OPTS=\"${kafka_gc_log_opts_prefix}\""
    }

    if $kafka_heap_opts {
      $kafka_heap_opts_real = "KAFKA_HEAP_OPTS=\"${kafka_heap_opts}\""
    }
    else {
      $kafka_heap_opts_real = ''
    }

    if $kafka_jmx_opts {
      $kafka_jmx_opts_real = "KAFKA_JMX_OPTS=\"${kafka_jmx_opts}\""
    }
    else {
      $kafka_jmx_opts_real = ''
    }

    if $kafka_jvm_performance_opts {
      $kafka_jvm_performance_opts_real = "KAFKA_JVM_PERFORMANCE_OPTS=\"${kafka_jvm_performance_opts}\""
    }
    else {
      $kafka_jvm_performance_opts_real = ''
    }

    $kafka_log4j_opts_prefix = "-Dlog4j.configuration=file:${logging_config}"
    if $kafka_log4j_opts {
      $kafka_log4j_opts_real = "KAFKA_LOG4J_OPTS=\"${kafka_log4j_opts_prefix} ${kafka_log4j_opts}\""
    }
    else {
      $kafka_log4j_opts_real = "KAFKA_LOG4J_OPTS=\"${kafka_log4j_opts_prefix}\""
    }

    if $kafka_opts {
      $kafka_opts_real = "KAFKA_OPTS=\"${kafka_opts}\""
    }
    else {
      $kafka_opts_real = ''
    }

    supervisor::service { $kafka::service_name:
      ensure                 => $kafka::service_ensure,
      enable                 => $kafka::service_enable,
      command                => "${kafka::command} ${config}",
      directory              => '/',
      environment            => "JMX_PORT=${jmx_port},${kafka_gc_log_opts_real},${kafka_heap_opts_real},${kafka_jmx_opts_real},${kafka_jvm_performance_opts_real},${kafka_log4j_opts_real},${kafka_opts_real}",
      user                   => $kafka::user,
      group                  => $kafka::group,
      autorestart            => $kafka::service_autorestart,
      startsecs              => $kafka::service_startsecs,
      retries                => $kafka::service_retries,
      stdout_logfile_maxsize => $kafka::service_stdout_logfile_maxsize,
      stdout_logfile_keep    => $kafka::service_stdout_logfile_keep,
      stderr_logfile_maxsize => $kafka::service_stderr_logfile_maxsize,
      stderr_logfile_keep    => $kafka::service_stderr_logfile_keep,
      stopsignal             => 'INT',
      stopasgroup            => true,
      require                => Class['::supervisor'],
    }

    if $kafka::service_enable == true {
      exec { 'restart-kafka-broker':
        command     => "supervisorctl restart ${kafka::service_name}",
        path        => ['/usr/bin', '/usr/sbin', '/sbin', '/bin'],
        user        => 'root',
        refreshonly => true,
        subscribe   => File[$config],
        onlyif      => 'which supervisorctl &>/dev/null',
        require     => Class['::supervisor'],
      }
    }

  }

}
