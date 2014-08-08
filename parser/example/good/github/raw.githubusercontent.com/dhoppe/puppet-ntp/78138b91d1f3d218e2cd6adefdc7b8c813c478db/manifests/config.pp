define ntp::config($config, $local, $remote) {
  file { $name:
    owner   => 'root',
    group   => 'root',
    mode    => '0644',
    alias   => 'ntp.conf',
    content => template("ntp/common/etc/ntp-${config}.conf.erb"),
    notify  => Service['ntp'],
    require => Package['ntp'],
  }
}