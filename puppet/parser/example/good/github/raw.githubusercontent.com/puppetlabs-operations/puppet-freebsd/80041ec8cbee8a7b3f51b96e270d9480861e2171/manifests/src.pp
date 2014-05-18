# == Class: freebsd::src
#
# Installs the FreeBSD source from Subversion
#
# == Paramaters
#
# [*dir*]
#   The directory to store the soruce
# [*release*]
#   The version of FreeBSD to checkout
#
# == Examples
#
#  class { "freebsd::src": }
#
# == Authors
#
# Zach Leslie <xaque208@gmail.com>
#
# == Copyright
#
# Copyright 2013 Puppet Labs
#
class freebsd::src (
  $dir     = '/usr/src',
  $release = '9.2.0',
) {

  package { "devel/subversion": }

  exec { "checkout kernel source for ${release} on ${architecture}":
    command => "/usr/local/bin/svn co svn://svn.freebsd.org/base/release/${release}/ ${dir}/",
    creates => "${dir}/.svn",
    timeout => '3600',
    require => Package["devel/subversion"],
  }
}
