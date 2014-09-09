# Author: Kumina bv <support@kumina.nl>

# Class: kbp_opennebula
#
# Actions:
#  Generic stuff for OpenNebula.
#
# Depends:
#
class kbp_opennebula {
}

# Class: kbp_opennebula::server
#
# Actions:
#  Setup an OpenNebula server.
#
# Parameters:
#  private_key: The location of the private key. This will be transferred as a file resource, puppet:///modules will already be added in front of it.
#  one_password: The password for the oneadmin user.
#
# Depends:
#  gen_opennebula
#
class kbp_opennebula::server ($private_key, $public_key, $one_password, $datastore='/srv/one', $script_remote_dir='/var/lib/one/remotes') {
  class { 'gen_opennebula::server':
    private_key       => $private_key,
    public_key        => $public_key,
    one_password      => $one_password,
    datastore         => $datastore,
    script_remote_dir => $script_remote_dir,
  }

  @@file { $datastore:
    ensure  => directory,
    owner   => 'oneadmin',
    group   => 'cloud',
    tag     => 'kumina_opennebula',
    require => User['oneadmin'];
  }

  Host <<| tag == 'kumina_opennebula' |>>
}

class kbp_opennebula::client ($public_key, $private_key) {
  class { 'gen_opennebula::client':
    public_key  => $public_key,
    private_key => $private_key;
  }

  @@host { $fqdn:
    ip  => $external_ipaddress,
    tag => 'kumina_opennebula';
  }

  kbp_sudo::rule {
    'Allow oneadmin to use vconfig':
      entity            => 'oneadmin',
      command           => '/sbin/vconfig *',
      as_user           => 'root',
      password_required => false;
    'Allow oneadmin to use brctl':
      entity            => 'oneadmin',
      command           => '/sbin/brctl *',
      as_user           => 'root',
      password_required => false;
    'Allow oneadmin to use ip':
      entity            => 'oneadmin',
      command           => '/sbin/ip *',
      as_user           => 'root',
      password_required => false;
  }

  File <<| tag == 'kumina_opennebula' |>>

  Host <<| tag == 'kumina_opennebula' |>>
}

class kbp_opennebula::sunstone ($password) {
  include gen_base::python_numpy

  class { 'gen_opennebula::sunstone':
    password => $password,
  }

  kbp_ferm::rule { 'Allow VNC connections from OpenNebula Server':
    action   => 'ACCEPT',
    proto    => 'tcp',
    dport    => '5900:6000',
    saddr    => $external_ipaddress,
    ferm_tag => 'opennebula_support',
    exported => true;
  }
}
