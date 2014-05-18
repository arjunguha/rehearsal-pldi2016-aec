class ceilometer::api (
  $enabled              = true,
  $metering_api_port    = 8777
)  {
  include 'ceilometer::params'

  ceilometer_config {
    'DEFAULT/metering_api_port':           value => $metering_api_port
  }

  ceilometer::upstart {$::ceilometer::params::api_name:
    enabled => $enabled,
    require => Exec['ceilometer-install']
  }
}
