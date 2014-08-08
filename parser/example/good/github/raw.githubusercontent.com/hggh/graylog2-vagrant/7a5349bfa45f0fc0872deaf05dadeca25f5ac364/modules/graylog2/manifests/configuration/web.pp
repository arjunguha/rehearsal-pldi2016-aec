class graylog2::configuration::web {
  $graylog2_web_http_address = $graylog2::web_http_address
  $graylog2_web_http_port    = $graylog2::web_http_port
  $web_graylog2_server_address = $graylog2::web_graylog2_server_address
  $web_secret                  = $graylog2::web_secret
  $web_timezone                = $graylog2::web_timezone

  File {
    owner  => "root",
    group  => "root",
    notify => Service["graylog2-web"],
  }
  file { "/etc/default/graylog2-web":
    ensure  => present,
    mode    => "0644",
    content => template("graylog2/graylog2-web.default"),
  }

  file { "/etc/graylog2/web/graylog2-web-interface.conf":
    ensure  => present,
    content => template("graylog2/graylog2-web-interface.conf.erb"),
  }
}
