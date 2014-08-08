# == Class kafka::config
#
class kafka::config inherits kafka {

  file { $config:
    ensure  => file,
    owner   => root,
    group   => root,
    mode    => '0644',
    content => template($kafka::config_template),
  }

  file { $logging_config:
    ensure  => file,
    owner   => root,
    group   => root,
    mode    => '0644',
    content => template($kafka::logging_config_template),
  }

}
