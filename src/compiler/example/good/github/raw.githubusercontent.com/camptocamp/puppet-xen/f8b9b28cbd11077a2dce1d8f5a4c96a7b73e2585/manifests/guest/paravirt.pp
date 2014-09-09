#
# == Class: xen::guest::paravirt
#
# Class to include on para-virtualized guests
#
class xen::guest::paravirt {
  package { "kernel-xen": ensure => present }
}
