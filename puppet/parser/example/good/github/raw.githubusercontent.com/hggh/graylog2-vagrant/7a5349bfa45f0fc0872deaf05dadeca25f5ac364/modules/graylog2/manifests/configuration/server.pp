class graylog2::configuration::server {
  $password_secret = $graylog2::password_secret
  $root_password_sha2 = $graylog2::root_password_sha2
  File {
    owner  => "root",
    group  => "root",
    notify => Service["graylog2-server"],
  }

  file { "/etc/default/graylog2-server":
    ensure  => present,
    mode    => "0644",
    content => template("graylog2/graylog2-server.default"),
  }

  file { "/etc/graylog2/server/server.conf":
    ensure  => present,
    owner   => "_graylog2",
    mode    => "0640",
    content => template("graylog2/server.conf.erb"),
  }
}
