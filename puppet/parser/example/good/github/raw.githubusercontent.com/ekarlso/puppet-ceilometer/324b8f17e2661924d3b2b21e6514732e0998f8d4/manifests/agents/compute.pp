class ceilometer::agents::compute (
  $enabled        = true
) {
  include 'ceilometer::params'

  User<| title == $::ceilometer::params::user |> {
    groups +> [$::ceilometer::params::nova_group, $::ceilometer::params::libvirt_group]
  }

  ceilometer::upstart {$::ceilometer::params::agent_compute_name:
    enabled => $enabled,
    require => Exec['ceilometer-install']
  }
}
