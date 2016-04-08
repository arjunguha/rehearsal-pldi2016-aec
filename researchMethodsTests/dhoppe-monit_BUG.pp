# NOTE(jcollard): Added since the program is written to fail if it isn't
# squeeze
$::lsbdistcodename = 'squeeze'

define monit::service() {
  file { "/etc/monit/conf.d/${name}":
    owner   => 'root',
    group   => 'root',
    mode    => '0644',
    #source  => "puppet:///modules/monit/common/etc/monit/conf.d/${name}",
    notify  => Service['monit'],
    require => [
      File['/etc/monit/conf.d'], 
      Package['monit']
    ],
    ensure => file
  }
}

class monit {
	file { '/etc/default/monit':
		owner   => root,
		group   => root,
		mode    => '0644',
		alias   => 'monit',
		#source  => "puppet:///modules/monit/${::lsbdistcodename}/etc/default/monit",
		notify  => Service['monit'],
		require => Package['monit'],
	}

	file { '/etc/monit/conf.d':
		force   => true,
		purge   => true,
		recurse => true,
		owner   => root,
		group   => root,
		mode    => '0644',
		require => Package['monit'],
		ensure => file
	}

	file { '/etc/monit/monitrc':
		owner   => root,
		group   => root,
		mode    => '0600',
		alias   => 'monitrc',
		content => template("monit/${::lsbdistcodename}/etc/monit/monitrc.erb"),
		notify  => Service['monit'],
		require => Package['monit'],
	}

	package { 'monit':
		ensure => present,
	}

	service { 'monit':
		ensure     => running,
		enable     => true,
		hasrestart => true,
		hasstatus  => false,
		require    => [
			File['monit'],
			File['monitrc'],
			Package['monit']
		],
	}
}

/*

HACK(arjun): This is crazy. Let's not support overriding using inheritance.

class monit::disabled inherits monit {
  Service['monit'] {
		enable => false,
		ensure => stopped,
  }
}

*/

# Instantiate class and defined type (-Rian)
include monit

monit::service {"test": }

# vim: tabstop=3