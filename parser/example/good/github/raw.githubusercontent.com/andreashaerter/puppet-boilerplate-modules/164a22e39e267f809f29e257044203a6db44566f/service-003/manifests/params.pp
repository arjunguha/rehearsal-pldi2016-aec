# == Class: boilerplate::params
#
# This class exists to
# 1. Declutter the default value assignment for class parameters.
# 2. Manage internally used module variables in a central place.
#
# Therefore, many operating system dependent differences (names, paths, ...)
# are addressed in here.
#
#
# === Parameters
#
# This class does not provide any parameters.
#
#
# === Examples
#
# This class is not intended to be used directly.
#
#
# === Links
#
# * {Puppet Docs: Using Parameterized Classes}[http://j.mp/nVpyWY]
#
#
# === Authors
#
# * John Doe <mailto:john.doe@example.com>
#
class boilerplate::params {

  #### Default values for the parameters of the main module class, init.pp

  # ensure
  $ensure = 'present'

  # autoupgrade
  $autoupgrade = false

  # service status
  $status = 'enabled'

  # autoload_class
  $autoload_class = false

  # packages
  case $::operatingsystem { # see http://j.mp/x6Mtba for a list of known values
    'CentOS', 'Fedora', 'Scientific': {
      $package = [ 'FIXME/TODO' ]
    }
    'Debian', 'Ubuntu': {
      $package = [ 'FIXME/TODO' ]
    }
    default: {
      fail("\"${module_name}\" provides no package default value for \"${::operatingsystem}\"")
    }
  }

  # debug
  $debug = false



  #### Internal module values

  # service parameters (q.v. http://j.mp/q6J073)
  case $::operatingsystem { # see http://j.mp/x6Mtba for a list of known values
    'CentOS', 'Fedora', 'Scientific': {
      $service_name       = 'FIXME/TODO'
      $service_hasrestart = true
      $service_hasstatus  = true
      $service_pattern    = $service_name # string or any legal Ruby pattern
    }
    'Debian', 'Ubuntu': {
      $service_name       = 'FIXME/TODO'
      $service_hasrestart = true
      $service_hasstatus  = true
      $service_pattern    = $service_name # string or any legal Ruby pattern
    }
    default: {
      fail("\"${module_name}\" provides no service parameters for \"${::operatingsystem}\"")
    }
  }

}
