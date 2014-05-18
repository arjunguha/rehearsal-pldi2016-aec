
class collectd {

	include collectd::install
	include collectd::configure
	include collectd::service

	Class['collectd::install'] -> Class['collectd::configure'] ~> Class['collectd::service']

}
