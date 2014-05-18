# Shared Certificates for Puppet Masters
#
# This class is intended to be run in a oneoff scenario to aid in the
# bootstrapping of a shared ca environment.  It is not meant to be
# permanantly installed as part of a maintained Puppet environment.
#
class pe_shared_ca (
  $ca_server,
  $purge_certs         = true,
  $manage_puppet_conf  = true,
  $puppet_user         = $pe_shared_ca::params::puppet_user,
  $puppet_group        = $pe_shared_ca::params::puppet_group,
  $services            = $pe_shared_ca::params::services,
  $source_uri          = "puppet:///modules/${module_name}/ssl",
  $mco_credentials_uri = "puppet:///modules/${module_name}/credentials",
) inherits pe_shared_ca::params {
  validate_bool($ca_server)

  ## Stop services before purging cert files
  service { $services:
    ensure  => 'stopped',
    before  => File[$mco_files_to_purge, $ca_files_to_purge],
  }

  if $purge_certs {
    ## Purge old ssl files
    file { $mco_files_to_purge:
      ensure  => absent,
      recurse => true,
      force   => true,
      before  => File['/etc/puppetlabs/mcollective/credentials'],
    }
    file { $ca_files_to_purge:
      ensure  => absent,
      recurse => true,
      force   => true,
      before  => File['/etc/puppetlabs/mcollective/credentials'],
    }
  }

  if $ca_server {
    ## Update CA directory and remove all pre-existing files
    file { "/etc/puppetlabs/puppet/ssl/ca":
      ensure  => directory,
      owner   => $puppet_user,
      group   => $puppet_group,
      source  => "${source_uri}/ca",
      recurse => true,
      purge   => true,
      force   => true,
      require => File[$ca_files_to_purge, $mco_files_to_purge],
    }
    if $manage_puppet_conf {
      ini_setting { 'master ca setting':
        path    => '/etc/puppetlabs/puppet/puppet.conf',
        section => 'master',
        setting => 'ca',
        value   => 'true',
      }
    }
  } else {
    ## Remove CA directory from non-ca-server
    file { "/etc/puppetlabs/puppet/ssl/ca":
      ensure  => absent,
      recurse => true,
      force   => true,
    }
    if $manage_puppet_conf {
      ini_setting { 'master ca setting':
        path    => '/etc/puppetlabs/puppet/puppet.conf',
        section => 'master',
        setting => 'ca',
        value   => 'false',
      }
    }
  }

  ## Update pe-internal certs
  file { "/etc/puppetlabs/puppet/ssl/certs":
    ensure  => directory,
    owner   => $puppet_user,
    group   => $puppet_group,
    source  => "${source_uri}/certs",
    recurse => true,
  }
  ## Update pe-internal private_keys
  file { "/etc/puppetlabs/puppet/ssl/private_keys":
    ensure  => directory,
    owner   => $puppet_user,
    group   => $puppet_group,
    mode    => '0640',
    source  => "${source_uri}/private_keys",
    recurse => true,
  }
  ## Update pe-internal public_keys
  file { "/etc/puppetlabs/puppet/ssl/public_keys":
    ensure  => directory,
    owner   => $puppet_user,
    group   => $puppet_group,
    source  => "${source_uri}/public_keys",
    recurse => true,
  }
  ## Update MCO credentials file
  file { "/etc/puppetlabs/mcollective/credentials":
    ensure => file,
    owner  => $puppet_user,
    group  => $puppet_group,
    source => $mco_credentials_uri,
    mode   => '0600',
  }
}
