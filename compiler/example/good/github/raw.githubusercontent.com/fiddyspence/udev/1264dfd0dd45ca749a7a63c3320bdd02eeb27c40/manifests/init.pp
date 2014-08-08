# == Class: udev
#
# Full description of class udev here.
#
# === Parameters
#
# Document parameters here.
#
# [*sample_parameter*]
#   Explanation of what this parameter affects and what it defaults to.
#   e.g. "Specify one or more upstream ntp servers as an array."
#
# === Variables
#
# Here you should define a list of variables that this module would require.
#
# [*sample_variable*]
#   Explanation of how this variable affects the funtion of this class and if it
#   has a default. e.g. "The parameter enc_ntp_servers must be set by the
#   External Node Classifier as a comma separated list of hostnames." (Note,
#   global variables should not be used in preference to class parameters  as of
#   Puppet 2.6.)
#
# === Examples
#
#  class { udev:
#  }
#
# === Authors
#
# Author Name <author@domain.com>
#
# === Copyright
#
# Copyright 2011 Your name here, unless otherwise noted.
#
class udev {

  if ! $::kernel == "Linux" {
    fail('Do not include the udev class on things that are not Linux')
  } 
   
  if ! $::ipaddress_eth0 and ! $::puppet_udev {
    file { '/etc/udev/rules.d/70-persistent-net.rules':
      ensure  => present,
      owner   => 'root',
      group   => 'root',
      mode    => '0644',
      content => template('udev/70-persistent-net.rules.erb'),
    } 
    file { '/etc/puppet_udev':
      ensure  => present,
      content => 'run',
      owner   => 'root',
      group   => 'root',
      mode    => '0644',
      require => File['/etc/udev/rules.d/70-persistent-net.rules'],
    }
  } 

}
