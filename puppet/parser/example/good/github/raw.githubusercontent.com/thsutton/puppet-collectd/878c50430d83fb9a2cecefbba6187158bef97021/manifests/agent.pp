#
# Class: collectd::agent
#
# Manages the configuration of a collectd collection agent.
#
# Parameters:
#   [*address*]  - address of the server to send to.
#   [*port*]     - port the server is listening on.
#   [*username*] - username to authenticate to the server.
#   [*password*] - password to authenticate to the server.
#   [*plugins*]  - list of plugins to enable.
#
# Actions:
#
# Requires:
#
# Sample Usage:
#
#   class { 'collectd::agent' :
#       address => "192.268.1.1",
#       username => "anony",
#       password => "mouse",
#   }
#
class collectd::agent (
	$address,
	$port = $collectd::params::port,
	$username,
	$password,
	$plugins = $collectd::params::plugins
) inherits collectd::params {

	class { 'collectd::configure' :
		forward_address => $address,
		forward_port => $port,
		network_username => $username,
		network_password => $password,
		plugins => $plugins,
	}

	include collectd::install
	include collectd::service

	Class['collectd::install'] -> Class['collectd::agent'] -> Class['collectd::service']

}
