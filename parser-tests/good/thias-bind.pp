# From https://github.com/thias/puppet-bind
# Changed usage of selector syntax on a boolean to an if-then-else expression.

# Class: bind
#
# Install and enable an ISC BIND server.
#
# Parameters:
#  $chroot:
#   Enable chroot for the server. Default: false
#  $packagenameprefix:
#   Package prefix name. Default: 'bind' or 'bind9' depending on the OS
#
# Sample Usage :
#  include bind
#  class { 'bind':
#    chroot            => true,
#    packagenameprefix => 'bind97',
#  }
#
class bind (
  $chroot            = false,
  $service_reload    = true,
  $packagenameprefix = $::bind::params::packagenameprefix,
) inherits ::bind::params {

  # Main package and service
  $packagenamesuffix = if $chroot {
    '-chroot'
  } else {
    ''    
  }
  class { 'bind::package':
    packagenameprefix => $packagenameprefix,
    packagenamesuffix => $packagenamesuffix,
  }
  class { 'bind::service':
    servicename    => $servicename,
    service_reload => $service_reload,
  }

  # We want a nice log file which the package doesn't provide a location for
  $bindlogdir = if $chroot {
    '/var/named/chroot/var/log/named'
  } else {
    '/var/log/named'
  }
  file { $bindlogdir:
    require => Class['bind::package'],
    ensure  => directory,
    owner   => $::bind::params::binduser,
    group   => $::bind::params::bindgroup,
    mode    => '0770',
    seltype => 'var_log_t',
    before  => Class['bind::service'],
  }

}

# Class: bind::package
#
class bind::package (
  $packagenameprefix = $::bind::params::packagenameprefix,
  $packagenamesuffix = '',
) inherits ::bind::params {

  package { "${packagenameprefix}${packagenamesuffix}": ensure => installed }

}

# Class: bind::params
#
class bind::params {

  case $::osfamily {
    'RedHat': {
      $packagenameprefix = 'bind'
      $servicename       = 'named'
      $binduser          = 'root'
      $bindgroup         = 'named'
    }
    'Debian': {
      $packagenameprefix = 'bind9'
      $servicename       = 'bind9'
      $binduser          = 'bind'
      $bindgroup         = 'bind'
    }
    'Freebsd': {
      $packagenameprefix = 'bind910'
      $servicename       = 'named'
      $binduser          = 'bind'
      $bindgroup         = 'bind'
    }
    default: {
      $packagenameprefix = 'bind'
      $servicename       = 'named'
      $binduser          = 'root'
      $bindgroup         = 'named'
    }
  }

}

# Class: bind::server
#
# For backwards compatibility. Use the main bind class instead.
#
class bind::server (
  $chroot            = false,
  $packagenameprefix = $bind::params::packagenameprefix
) inherits bind::params {
  class { 'bind':
    chroot            => $chroot,
    packagenameprefix => $packagenameprefix,
  }
}

# Class: bind::service
#
class bind::service (
  $servicename    = $::bind::params::servicename,
  $service_reload = true,
) inherits ::bind::params {

  if $service_reload {
    Service[$servicename] {
      restart => "service ${servicename} reload",
    }
  }

  service { $servicename :
    require   => Class['bind::package'],
    hasstatus => true,
    enable    => true,
    ensure    => running,
  }

}
