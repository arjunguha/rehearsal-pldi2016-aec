class ceilometer::params {
  $api_name           = 'ceilometer-api'
  $agent_central_name = 'ceilometer-agent-central'
  $agent_compute_name = 'ceilometer-agent-compute'
  $collector_name     = 'ceilometer-collector'

  $user               = 'ceilometer'
  $group              = 'ceilometer'

  $nova_group         = 'nova'
  $libvirt_group      = 'libvirtd'

  $source             = 'git://github.com/stackforge/ceilometer'
  $install_dir        = '/opt/ceilometer'
  $revision           = 'master'
}
