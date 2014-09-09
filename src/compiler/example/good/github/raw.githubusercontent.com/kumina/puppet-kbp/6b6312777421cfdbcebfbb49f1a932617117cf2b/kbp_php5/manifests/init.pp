# Author: Kumina bv <support@kumina.nl>

# Class: kbp_php5::common
#  Actions: Default config for PHP.
#
class kbp_php5::common {
  gen_php5::common::config { 'Do not expose PHP versions':
    ensure   => present,
    variable => 'expose_php',
    value    => 'Off';
  }
}

# Class: kbp_php5::curl
#
# Actions:
#  Install curl extensions for PHP5.
#
# Depends:
#  gen_puppet
#
class kbp_php5::curl {
  class { "gen_php5::curl":
    notify => Exec["reload-apache"];
  }
}

class kbp_php5::apc($shm_size=64, $ttl=3600, $shm=true, $shm_size_with_suffix=false) {
  include kbp_collectd::plugin::php_apc
  if versioncmp($lsbmajdistrelease, 6) > 0 {
    $real_suffix = true
  } else {
    $real_suffix = $shm_size_with_suffix
  }

  class { 'gen_php5::apc':
    shm_size             => $shm_size,
    shm_size_with_suffix => $real_suffix,
    shm                  => $shm,
    ttl                  => $ttl;
  }

  file { '/var/www/apc_info.php':
    ensure => symlink,
    target => '/usr/share/munin/plugins/kumina/apc_info.php';
  }

  gen_munin::client::plugin { ['php_apc_files', 'php_apc_fragmentation', 'php_apc_hit_miss', 'php_apc_purge', 'php_apc_rates', 'php_apc_usage', 'php_apc_mem_size', 'php_apc_user_hit_miss', 'php_apc_user_entries', 'php_apc_user_rates']:
    script_path => '/usr/share/munin/plugins/kumina',
    script      => 'php_apc_';
  }

  gen_munin::client::plugin::config { 'php_apc':
    section => 'php_apc_*',
    content => "env.url http://127.0.0.255/apc_info.php?auto\n";
  }
}

class kbp_php5::xsl {
  include gen_php5::xsl
}

# Define: kbp_php5::config
#
# Actions:
#
define kbp_php5::config ($ensure='present', $value=false, $variable=false) {
  include kbp_php5::common

  gen_php5::common::config { $name:
    ensure   => $ensure,
    value    => $value,
    variable => $variable;
  }

  if $name == 'upload_max_filesize' {
    file { '/etc/apache2/conf.d/fcgi_max_requestlength':
      require => Package['apache2'],
      notify  => Exec['reload-apache2'],
      content => "<IfModule mod_fcgid.c>\nFcgidMaxRequestLen ${value}\n</IfModule>\n";
    }
  }

  if $name == 'post_max_size' {
    kbp_php5::config { 'upload_max_filesize':
      ensure   => $ensure,
      value    => $value;
     }
  }
}
