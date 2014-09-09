class graylog2::packages {
  package { 'graylog2-server':
    ensure => latest,
    notify => Service["graylog2-server"],
  }
  package { 'graylog2-web':
    ensure => latest,
    notify => Service["graylog2-web"],
  }
  package { 'graylog2-stream-dashboard':
    ensure => latest,
  }
}
