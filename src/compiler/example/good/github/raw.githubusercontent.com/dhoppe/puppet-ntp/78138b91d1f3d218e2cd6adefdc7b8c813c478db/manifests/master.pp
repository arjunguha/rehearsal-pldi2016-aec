class ntp::master inherits ntp {
  Ntp::Config['/etc/ntp.conf'] {
    config => 'server',
  }
}