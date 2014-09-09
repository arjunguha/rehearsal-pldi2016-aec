# $Id$

class icinga::check::raid::software (
  $ensure = "present") {
  $prese_real = $ensure ? {
    "absent" => "absent",
    default  => $has_raid ? {
      "false" => "absent",
      default => $ensure
    } }

  icinga::nrpe_plugin { "${fqdn}_checkraid":
    service_description  => "CHECKRAID",
    command_name         => "check_raid",
    servicegroups        => "Harddrives",
    notification_options => "w,c,u",
    ensure               => $prese_real,
  }
}

class icinga::check::raid::three_ware (
  $ensure = "present") {
  $prese_real = $ensure ? {
    "absent" => "absent",
    default  => $has_raid ? {
      "false" => "absent",
      default => $ensure,
    } }

  icinga::nrpe_plugin { "${fqdn}_checkraid":
    service_description  => "CHECKRAID",
    command_name         => "check_3ware_raid",
    notification_options => "w,c,u",
    sudo                 => true,
    servicegroups        => "Harddrives",
    ensure               => $prese_real,
  }
}

