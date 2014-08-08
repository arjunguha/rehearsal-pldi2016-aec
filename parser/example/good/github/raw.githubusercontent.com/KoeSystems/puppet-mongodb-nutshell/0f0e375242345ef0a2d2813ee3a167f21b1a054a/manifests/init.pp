# == Class: mongodb
#
# MongoDB in a nutshell.
#
# === Parameters
#
# MongoDB parameters are in params.pp subclass
#
# === Authors
#
# Koe <koe.systems@gmail.com>
#
# === Copyright
#
# Copyright 2013 Koe

class mongodb {
  class { 'mongodb::dependencies': }
  class { 'mongodb::install': }
}
