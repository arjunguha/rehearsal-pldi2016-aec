# Node styles for the EXAMPLE2 environment
# vim: ts=2: sw=2
#
node ex2_style {
	$my_site = 'ex2'
	$my_domain = 'example2.net'
	$my_hostips_dns = [ '10.250.250.5' ]
	$my_search_domains = [ 'example2.net' ]
	$my_opencsw_mirror = 'http://evil/mirrors/opencsw/current'
	$my_gems_mirror = 'http://evil/mirrors/gems.rubyforge.org'
	$my_puppet_version = '0.25.4'
	$my_puppet_runinterval = '1800'
}

# puppet master
node ex2_style_puppetmaster inherits ex2_style { 
  $my_loghost = '127.0.0.1'
}

# puppet slave
node ex2_style_puppetslave inherits ex2_style {
  $my_loghost = '127.0.0.1'
	$my_puppet_version = '0.25.5'
	$my_passenger_version = '3.0.2'
}

