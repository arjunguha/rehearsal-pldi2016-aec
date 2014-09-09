class graylog2::service {
  service { "graylog2-server":
    ensure => running,
  }
  service { "graylog2-web":
    ensure => running,
  }
}
