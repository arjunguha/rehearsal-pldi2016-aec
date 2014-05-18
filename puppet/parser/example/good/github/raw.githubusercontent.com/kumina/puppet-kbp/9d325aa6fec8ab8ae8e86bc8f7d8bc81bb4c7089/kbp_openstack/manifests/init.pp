# Author: Kumina bv <support@kumina.nl>

# Class: kbp_openstack
#
# Actions:
#  Generic stuff for OpenStack.
#
# Depends:
#
class kbp_openstack {
}

# Class: kbp_openstack::apt_setup
#
# Actions:
#  Setup the apt repositories to get the version of OpenStack that we want.
#
# Depends:
#
class kbp_openstack::apt_setup {
  if $lsbdistcodename == 'wheezy' {
    gen_apt::source {
      "openstack":
        uri          => "http://archive.gplhost.com/debian",
        distribution => "grizzly",
        key          => 'FEFFE51F',
        components   => ["main"];
      "openstack-backports":
        uri          => "http://archive.gplhost.com/debian",
        distribution => "grizzly-backports",
        key          => 'FEFFE51F',
        components   => ["main"];
    }

    gen_apt::key { 'FEFFE51F':; }
  } else {
    fail("This has not been tested for ${lsbdistcodename}.")
  }
}

# Class: kbp_openstack::server
#
# Actions:
#  Setup an OpenStack server.
#
# Depends:
#  gen_openstack
#
class kbp_openstack::server ($rabbitmq_ssl_key, $rabbitmq_ssl_cert) {
  include gen_openstack::server
  include gen_base::memcached
  class {
    'kbp_mysql::server':
      mysql_tag         => 'openstack',
      datadir           => '/srv/mysql';
    'kbp_rabbitmq':
      ssl_cert          => template($rabbitmq_ssl_cert),
      ssl_key           => template($rabbitmq_ssl_key),
      namespace         => "/openstack",
      rabbitmq_name     => 'openstack',
      upstream_packages => false;
  }
}

# Class: kbp_openstack::client
#
# Actions:
#  Setup an OpenStack host.
#
# Depends:
#  gen_openstack
#
class kbp_openstack::client {
}
