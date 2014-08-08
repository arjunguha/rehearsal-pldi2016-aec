# $Id$

define icinga::servicegroup (
  $servicegroup_name    = "",
  $servicegroup_alias   = "",
  $servicegroup_members = "",
  $ensure               = "present") {
  $servicegroup_name_real = $servicegroup_name ? {
    ""      => $name,
    default => $servicegroup_name,
  }

  icinga::object { "servicegroup_${servicegroup_name_real}":
    content => template("icinga/servicegroup.erb"),
    ensure  => $ensure,
  }
}
