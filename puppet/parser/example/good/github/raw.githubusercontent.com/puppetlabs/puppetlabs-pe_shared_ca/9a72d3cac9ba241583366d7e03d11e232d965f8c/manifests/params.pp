class pe_shared_ca::params {

  $ca_files_to_copy = [
    "ca/ca_crl.pem",
    "ca/ca_crt.pem",
    "ca/ca_key.pem",
    "ca/ca_pub.pem",
    "certs/pe-internal-broker.pem",
    "certs/pe-internal-mcollective-servers.pem",
    "certs/pe-internal-peadmin-mcollective-client.pem",
    "certs/pe-internal-puppet-console-mcollective-client.pem",
    "private_keys/pe-internal-broker.pem",
    "private_keys/pe-internal-mcollective-servers.pem",
    "private_keys/pe-internal-peadmin-mcollective-client.pem",
    "private_keys/pe-internal-puppet-console-mcollective-client.pem",
    "public_keys/pe-internal-broker.pem",
    "public_keys/pe-internal-mcollective-servers.pem",
    "public_keys/pe-internal-peadmin-mcollective-client.pem",
    "public_keys/pe-internal-puppet-console-mcollective-client.pem",
  ]
  $mco_credentials_file = '/etc/puppetlabs/mcollective/credentials'

  # Setup variables to represent various files this class will manipulate
  $ca_files_to_purge = [
    "/etc/puppetlabs/puppet/ssl/certs/ca.pem",
    "/etc/puppetlabs/puppet/ssl/certs/${::clientcert}.pem",
    "/etc/puppetlabs/puppet/ssl/private_keys/${::clientcert}.pem",
    "/etc/puppetlabs/puppet/ssl/public_keys/${::clientcert}.pem",
    "/etc/puppetlabs/puppet/ssl/crl.pem",
  ]
  $mco_files_to_purge = [
    "/etc/puppetlabs/mcollective/ssl",
    "/etc/puppetlabs/activemq/broker.ks",
    "/etc/puppetlabs/activemq/broker.p12",
    "/etc/puppetlabs/activemq/broker.pem",
    "/etc/puppetlabs/activemq/broker.ts",
  ]

  $puppet_user  = 'pe-puppet'
  $puppet_group = 'pe-puppet'
  case $::osfamily {
    'debian': {
      $services     = [
        'pe-puppet-agent',
        'pe-httpd',
        'pe-mcollective',
        'pe-activemq',
      ]
    }
    'redhat': {
      $services     = [
        'pe-puppet',
        'pe-httpd',
        'pe-mcollective',
        'pe-activemq',
      ]
    }
  }
}
