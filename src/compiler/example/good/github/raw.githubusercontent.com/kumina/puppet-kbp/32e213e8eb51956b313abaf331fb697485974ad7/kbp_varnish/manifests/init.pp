# Author: Kumina bv <support@kumina.nl>

# Class: kbp_varnish
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_varnish {
  include gen_varnish
  include kbp_collectd::plugin::varnish

  kbp_backup::exclude {
    "varnish data lib":   content => "/var/lib/varnish/*";
    "varnish data cache": content => "/var/cache/varnish/*";
  }

  if $lsbdistcodename == 'squeeze' {
    gen_apt::preference { 'varnish':; }
  } elsif $lsbdistcodename == 'wheezy' {
    # Use the default
  } else {
    fail("Not tested for ${lsbdistcodename}.")
  }

  # Setup munin trending
  munin_plugin_helper { ['ratio', 'backend_req', 'client_req', 'sms_balloc', 'sms_bfree', 'cache_hit', 'cache_miss', 'n_object', 's_bodybytes', 's_hdrbytes']:; }

  # we want logging on disk
  file { '/etc/default/varnishlog':
    content => 'VARNISHLOG_ENABLED=1',
    require => Package['varnish'],
    notify  => Exec['reload varnishlog'];
  }

  exec { 'reload varnishlog':
    command     => '/etc/init.d/varnishlog restart',
    refreshonly => true,
  }

  # We want logging accessible for the adm team
  file { '/var/log/varnish':
    owner => 'varnishlog',
    group => 'adm';
  }
}

class kbp_varnish::config ($nfiles='131072',$memlock='82000',$vcl_conf='/etc/varnish/default.vcl',$listen_address='',$listen_port='6081',$admin_address='127.0.0.1',
                           $admin_port='6082',$min_threads='1',$max_threads='1000',$idle_timeout='120',$storage_file='/var/lib/varnish/varnish_storage.bin',
                           $storage_size='1G',$secret_file='/etc/varnish/secret',$default_ttl='120') {
  include kbp_varnish

  gen_varnish::config { $name:
    nfiles         => $nfiles,
    memlock        => $memlock,
    vcl_conf       => $vcl_conf,
    listen_address => $listen_address,
    listen_port    => $listen_port,
    admin_address  => $admin_address,
    admin_port     => $admin_port,
    min_threads    => $min_threads,
    max_threads    => $max_threads,
    idle_timeout   => $idle_timeout,
    storage_file   => $storage_file,
    storage_size   => $storage_size,
    secret_file    => $secret_file,
    default_ttl    => $default_ttl;
  }
}

define munin_plugin_helper {
  gen_munin::client::plugin { "varnish_${name}":
    script_path => "/usr/share/munin/plugins/kumina/",
    script      => "varnish_",
  }
}
