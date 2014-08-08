class ntp::client {
  case $::osfamily {
    'Debian': { include ::ntp::client::debian }
    'RedHat': { include ::ntp::client::rhel }
    default: { fail "Unknown OS family ${::osfamily}" }
  }
}
