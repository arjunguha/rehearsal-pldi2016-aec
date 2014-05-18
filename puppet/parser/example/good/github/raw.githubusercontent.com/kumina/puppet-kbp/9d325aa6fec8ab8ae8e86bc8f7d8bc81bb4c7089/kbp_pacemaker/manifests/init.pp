# Author: Kumina bv <support@kumina.nl>

# Copyright (C) 2010 Kumina bv, Ed Schouten <ed@kumina.nl>
# This works is published under the Creative Commons Attribution-Share
# Alike 3.0 Unported license - http://creativecommons.org/licenses/by-sa/3.0/
# See LICENSE for the full legal text.

# Class: kbp_pacemaker
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_pacemaker {
  include kbp_icinga::pacemaker
  include gen_pacemaker

  file { '/usr/lib/ocf/resource.d/heartbeat/MailTo':
    content => template('kbp_pacemaker/MailTo'),
    mode    => 755,
    require => Package['pacemaker'];
  }

  kbp_pacemaker::primitive { 'mail_alert':
    provider => 'ocf:heartbeat:MailTo',
    params   => "email=\"reports+${environment}@kumina.nl\" subject=\"Cluster Failover\"";
  }
}

class kbp_pacemaker::ip_sysctls {
  sysctl::setting {
    "net.ipv4.conf.all.arp_ignore":   value => 1;
    "net.ipv4.conf.all.arp_announce": value => 2;
  }
}

define kbp_pacemaker::primitive ($provider, $location=false, $location_score="inf", $location_name=false, $start_timeout=false, $monitor_interval=false, $monitor_timeout=false, $stop_timeout=false, $params=false, $group=false) {
  $safe_name = regsubst($name, '[^a-zA-Z0-9\-_]', '_', 'G')

  gen_pacemaker::primitive { $safe_name:
    provider         => $provider,
    location         => $location,
    location_score   => $location_score,
    location_name    => $location_name,
    start_timeout    => $start_timeout,
    stop_timeout     => $stop_timeout,
    monitor_interval => $monitor_interval,
    monitor_timeout  => $monitor_timeout,
    group            => $group,
    params           => $params;
  }

  if $provider == 'ocf:heartbeat:IPaddr2' {
    include kbp_pacemaker::ip_sysctls
  }
}


define kbp_pacemaker::master_slave ($primitive, $meta) {
  gen_pacemaker::master_slave { $name:
    primitive => $primitive,
    meta      => $meta;
  }
}

define kbp_pacemaker::location ($primitive, $score="inf", $resnode) {
  gen_pacemaker::location { $name:
    primitive => $primitive,
    score     => $score,
    resnode   => $resnode;
  }
}

define kbp_pacemaker::colocation ($ensure='present', $resource_1, $resource_2, $score="inf") {
  if $ensure == 'present' {
    gen_pacemaker::colocation { $name:
      resource_1 => $resource_1,
      resource_2 => $resource_2,
      score      => $score;
    }
  }
}

define kbp_pacemaker::order ($ensure='present', $score="inf", $resource_1, $resource_2) {
  if $ensure == 'present' {
    gen_pacemaker::order { $name:
      resource_1 => $resource_1,
      resource_2 => $resource_2,
      score      => $score;
    }
  }
}

define kbp_pacemaker::group {
  gen_pacemaker::group { $name:; }
}

define kbp_pacemaker::clone ($resource) {
  gen_pacemaker::clone { $name:
    resource => $resource;
  }
}
