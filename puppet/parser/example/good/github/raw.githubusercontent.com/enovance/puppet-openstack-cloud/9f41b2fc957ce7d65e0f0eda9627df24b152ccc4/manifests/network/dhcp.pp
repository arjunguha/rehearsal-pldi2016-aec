#
# Copyright (C) 2014 eNovance SAS <licensing@enovance.com>
#
# Licensed under the Apache License, Version 2.0 (the "License"); you may
# not use this file except in compliance with the License. You may obtain
# a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
# License for the specific language governing permissions and limitations
# under the License.
#
# Network DHCP node
#

class cloud::network::dhcp(
  $veth_mtu           = 1500,
  $debug              = true,
  $dnsmasq_dns_server = false
) {

  include 'cloud::network'

  class { 'neutron::agents::dhcp':
    debug => $debug
  }

  neutron_dhcp_agent_config {
    'DEFAULT/dnsmasq_config_file':      value => '/etc/neutron/dnsmasq-neutron.conf';
    'DEFAULT/enable_isolated_metadata': value => true;
  }
  if $dnsmasq_dns_server {
    neutron_dhcp_agent_config { 'DEFAULT/dnsmasq_dns_server':
      value => $dnsmasq_dns_server
    }
  } else {
    neutron_dhcp_agent_config { 'DEFAULT/dnsmasq_dns_server':
      ensure => absent
    }
  }

  file { '/etc/neutron/dnsmasq-neutron.conf':
    content => template('cloud/network/dnsmasq-neutron.conf.erb'),
    owner   => 'root',
    mode    => '0755',
    group   => 'root',
    notify  => Service['neutron-dhcp-agent']
  }

}