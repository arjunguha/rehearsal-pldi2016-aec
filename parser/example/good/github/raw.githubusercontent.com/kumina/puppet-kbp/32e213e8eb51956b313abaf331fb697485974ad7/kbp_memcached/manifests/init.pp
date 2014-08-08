# Author: Kumina bv <support@kumina.nl>

# Class: kbp_memcached
#
# Actions:
#  Setup memcached the way we like it.
#
# Depends:
#  gen_base
#
class kbp_memcached {
  # TODO probably need to setup gen_memcached if we actually going to do config setting with this
  include gen_base::memcached
  include kbp_munin::client::memcached
  include kbp_collectd::plugin::memcached
}
