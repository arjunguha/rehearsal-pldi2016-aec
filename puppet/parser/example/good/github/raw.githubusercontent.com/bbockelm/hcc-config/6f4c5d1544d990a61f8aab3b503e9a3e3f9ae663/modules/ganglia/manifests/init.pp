#
# Class: ganglia
#
# manages ganglia
#
class ganglia {

	include ganglia::params, ganglia::install, ganglia::config, ganglia::service

}
