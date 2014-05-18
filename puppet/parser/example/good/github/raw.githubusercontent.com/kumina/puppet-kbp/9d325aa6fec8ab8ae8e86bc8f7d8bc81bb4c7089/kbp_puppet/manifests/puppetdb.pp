# Class: kbp_puppet::puppetdb
#
# Action: Install the package.
#
# Depends:
#  gen_puppet
#
class kbp_puppet::puppetdb {
  include gen_puppet::puppetdb
}

# Define: kbp_puppet::puppetdb::config
#
# Action: Setup configuration parameters for a puppetdb.
#
# Parameters:
#  None, for the time being.
#
# Depends:
#  gen_puppet
#
define kbp_puppet::puppetdb::config () {
  include kbp_puppet::puppetdb

  gen_puppet::puppetdb::set_config {
    "server": value => $fqdn;
    "port":   value => '8081';
  }

  gen_puppet::set_config {
    "storeconfigs":
      section => 'main',
      value   => 'true';
    "storeconfigs_backend":
      section => 'main',
      value   => 'puppetdb';
  }
}
