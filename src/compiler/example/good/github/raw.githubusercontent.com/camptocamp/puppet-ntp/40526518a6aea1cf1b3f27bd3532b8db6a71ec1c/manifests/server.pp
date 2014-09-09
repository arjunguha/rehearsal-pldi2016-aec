class ntp::server {
  case $::osfamily {
    'Debian': { include ::ntp::server::debian }
    default: { fail "Unkown OS family ${::osfamily}" }
  }
}
