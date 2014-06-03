node default {
  include foreman
  include foreman_proxy
  include puppet
  include puppet::server
}
