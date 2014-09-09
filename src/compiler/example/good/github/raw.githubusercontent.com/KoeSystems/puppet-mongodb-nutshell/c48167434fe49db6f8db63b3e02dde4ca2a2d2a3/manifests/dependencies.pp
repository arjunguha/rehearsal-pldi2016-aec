# == Class: mongodb::dependencies
#
# Class to manage mongodb dependencies. Allow to install x86 or amd64 binaries.
#
# === Authors
#
# Koe <koe.systems@gmail.com>
#
# === Copyright
#
# Copyright 2013 Koe
#

class mongodb::dependencies {
  case $::architecture {
    amd64: { require mongodb::dependencies::amd64 }
    x86: { require mongodb::dependencies::x86 }
    default: { notify('Only linux x86 and amd64 are supported') }
  }
}
