# = Class: puppet::client::solaris
#
# == Description
#
# Overrides and solaris-specfic resources 
#
# == Usage
# This class is meant to be included from the puppet::client class
class puppet::client::solaris inherits puppet::client {

	include packages

	Package <| title == ruby18 |>
	Package <| title == rubygems |>
	Package <| title == libruby1 |>
	Package <| title == berkeleydb47 |>
	Package <| title == readline |>
	Package <| title == common |>
	Package <| title == ncurses |>
	Package <| title == terminfo |>

	# Overrides 
	Service[puppet] {
		name => 'puppetd',
		subscribe +> File[puppetd-smf-method],
		manifest => "${rubysitedir}/../../gems/1.8/gems/puppet-${puppetversion}/conf/solaris/smf/puppetd.xml",
	}

  package {
    facter:
      ensure => installed,
      provider => gem,
      source => $my_gems_mirror,
      require => Package[rubygems];
    puppet:
      ensure => $my_puppet_version,
			provider => gem,
			source => $my_gems_mirror,
			require => Package[facter];
	}

	# We do not want the opencsw packages installed
	# But only remove them if the gem packages are installed
	package { 
		[ CSWfacter, CSWpuppet, RELpuppet ]:
			ensure => absent,
			provider => sun,
			require => Package[puppet];
	}

	tools::gem_cleanup { puppet: subscribe => Package[puppet] }

	# symlinks
	file {
		'/usr/bin/gem':
			ensure => '/opt/csw/bin/gem',
			require => Package[rubygems];
		'/lib/svc/method/svc-puppetd':
			ensure => '/opt/csw/lib/svc/method/svc-puppetd',
			require => File[puppetd-smf-method];
	}

	# We need this to upgrade from opencsw packages
	file {
		'/opt/csw/lib/svc':
			ensure => directory,
			owner => 'root', 
			group => 'bin', 
			mode => 0755,
			require => Package[puppet];
		'/opt/csw/lib/svc/method':
			ensure => directory,
			owner => 'root', 
			group => 'bin', 
			mode => 0755;
	}

	# Drop the SMF method where opencsw used to store it
	# This way, we can avoid the need to reinstall a manifest
	file {
		puppetd-smf-method:
			path => '/opt/csw/lib/svc/method/svc-puppetd',
			ensure => present,
			owner => 'root', 
			group => 'bin', 
			mode => 0755,
			source => 'puppet:///modules/puppet/client/global/smf/svc-puppetd';
		puppetd-smf-manifest:
			path => '/tmp/puppetd.xml',
			ensure => absent,
			owner => 'root', 
			group => 'root', 
			mode => 0644,
			source => 'puppet:///modules/puppet/client/global/smf/puppetd.xml',
			require => Package[puppet],
			replace => true;
	}

}
