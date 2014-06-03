# Author: Kumina bv <support@kumina.nl>

class kbp_stunnel {
  file {
    '/etc/init.d/stunnel4':
      content => template('kbp_stunnel/stunnel4_init'),
      mode    => 755,
      require => Package['stunnel'];
    '/etc/default/stunnel4':
      content => template('kbp_stunnel/stunnel4_default'),
      notify  => Service['stunnel4'],
      require => Package['stunnel'];
  }

  concat { '/etc/stunnel/stunnel.conf':
    notify  => Service['stunnel4'],
    require => Package['stunnel'];
  }

  concat::add_content { 'global':
    content => template('kbp_stunnel/global.conf'),
    target  => '/etc/stunnel/stunnel.conf';
  }
}

# Define: kbp_stunnel::site
#
# Parameters:
#  port
#    Undocumented
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
define kbp_stunnel::site($ip, $cert=false, $key=false, $wildcard=false, $intermediate=false, $intermediate_file=false, $port=443) {
  include kbp_stunnel
  if $intermediate {
    include "kbp_ssl::intermediate::${intermediate}"

    $intermediate_name = template("kbp_ssl/translate_names.erb")
  }

  $real_cert = $cert ? {
    false   => $wildcard ? {
      false   => "${name}.pem",
      default => "${wildcard}.pem",
    },
    default => "${cert}.pem",
  }
  $real_key = $key ? {
    false   => $wildcard ? {
      false   => "${name}.key",
      default => "${wildcard}.key",
    },
    default => "${key}.key",
  }

  concat::add_content { "service_${name}":
    content => template('kbp_stunnel/service.conf'),
    target  => '/etc/stunnel/stunnel.conf';
  }

  kbp_ferm::rule { "Stunnel forward for ${name}":
    proto  => "tcp",
    daddr  => $ip,
    dport  => $port,
    action => "ACCEPT";
  }
}
