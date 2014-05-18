# $Id$

$NAGIOSCONFDIR = "/etc/icinga/objects"
$nrpe_d = $operatingsystem ? {
  "FreeBSD" => "/usr/local/etc/nrpe.d",
  "Darwin"  => "/opt/local/etc/nrpe/nrpe.d",
  default   => "/etc/nagios/nrpe.d",
}

define icinga::object (
  $path   = "",
  $content,
  $ensure = "present") {
  # nagios cannot read file with dots "."
  $name_real = convert($name, '.', '-')
  $path_real = $path ? {
    ""      => "/etc/icinga/objects/${name_real}",
    default => $path,
  }

  # notice("${fqdn}: Setting nagios3 name: ${name}, check:
  # ${name_real} and: ${path_real}")
  @@file { "${path_real}.cfg":
    ensure  => $ensure,
    content => $content,
    owner   => "nagios",
    group   => "www-data",
    tag     => "icinga_object",
    mode    => 0644,
    purge   => true,
  }
}

import "icinga_*.pp"
import "defines/*.pp"
import "classes/*.pp"
