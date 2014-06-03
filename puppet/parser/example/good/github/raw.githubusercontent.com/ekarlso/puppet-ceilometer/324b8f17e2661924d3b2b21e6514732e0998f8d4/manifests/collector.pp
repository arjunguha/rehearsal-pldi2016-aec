class ceilometer::collector (
  $enabled        = true
) {
  include 'ceilometer::params'

  User<| title == $::ceilometer::params::user |> { 
    groups +> [$::ceilometer::params::nova_group, $::ceilometer::params::libvirt_group]
  }

  ceilometer::upstart {$::ceilometer::params::collector_name:
    enabled => $enabled,
    require => Exec['ceilometer-install']
  }
}
