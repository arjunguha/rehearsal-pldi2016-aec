class graylog2(
  $web_graylog2_server_address,
  $web_secret,
  $web_timezone,
  $password_secret,
  $root_password_sha2,
  $hggh_repro       = true,
  $web_http_address = "0.0.0.0",
  $web_http_port    = "9000",
  ) {

  if ($hggh_repro == true) {
    include graylog2::source
    Class['graylog2::source'] -> Class['graylog2::packages']
  }

  include graylog2::packages
  include graylog2::service
  include graylog2::configuration::web
  include graylog2::configuration::server

  Class['graylog2::packages'] -> Class['graylog2::service']
  Class['graylog2::packages'] -> Class['graylog2::configuration::web']
  Class['graylog2::packages'] -> Class['graylog2::configuration::server']

  file { "/usr/local/bin/create_graylog2_inputs_gelf":
    ensure => present,
    owner  => "root",
    group  => "root",
    mode   => "0755",
    source => "puppet:///modules/graylog2/create_graylog2_inputs_gelf",
  }

  exec { "create_gelf_udp_tcp_inputs":
    command   => "/usr/local/bin/create_graylog2_inputs_gelf",
    require   => Service['graylog2-server'],
    subscribe => [ File["/etc/graylog2/server/server.conf"], Service['graylog2-server'] ],
  }

  file { "/usr/local/create_test_message":
    ensure => present,
    owner  => "root",
    group  => "root",
    mode   => "0755",
    source => "puppet:///modules/graylog2/create_test_message",
  }

  cron { "create_test_messages":
    command => "/usr/local/create_test_message > /dev/null 2>&1",
    minute  => "*",
    user    => "root",
  }
}
