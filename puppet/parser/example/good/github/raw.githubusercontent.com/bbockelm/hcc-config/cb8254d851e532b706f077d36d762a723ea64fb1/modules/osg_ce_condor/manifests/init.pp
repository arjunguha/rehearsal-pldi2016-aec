#
# Class: osg_ce_condor
#
class osg_ce_condor (
  $gums_server = params_lookup( 'gums_server' ),
  $rms         = params_lookup( 'rms' ),
  $rms_config  = params_lookup( 'rms_config' ),
) inherits osg_ce_condor::params {

  stage { 'install_osg_ce_condor': before => Stage['main'] }

  # Install the RPMs first
  class { 'osg_ce_condor::install': stage => 'install_osg_ce_condor' }

  include osg_ce_condor::config, osg_ce_condor::service
  include osg_ce_condor::hostcert

}
