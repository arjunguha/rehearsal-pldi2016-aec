class ntp (
  $ntp_local  = $ntp::params::local,
  $ntp_remote = $ntp::params::remote
) inherits ntp::params {

  validate_hash(hiera('local'))
  validate_array(hiera('remote'))

  ntp::config { '/etc/ntp.conf':
    config => 'client',
    local  => $ntp_local,
    remote => $ntp_remote,
  }

  package { 'ntp':
    ensure => present,
  }

  service { 'ntp':
    ensure     => running,
    enable     => true,
    hasrestart => true,
    hasstatus  => true,
    require    => [
      File['ntp.conf'],
      Package['ntp']
    ],
  }
}