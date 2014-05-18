#
# Class kbp_logstash::server::receiver
#
# Actions:
#  Set up Logstash and redis. These machines receive logs from lumberjack and write them to redis for further processing
#
# Parameters:
#  redis_addresses: An array of IP addresses where the redis-servers live
#  key_location: The (puppet) location for the private key and the cert (passed top kbp_ssl::keys)
#  external_ip: The IP address we should listen on for lumberjack
#  internal_ip: The IP address we shoudl listen on for redis
#  lumberjack_port: take a guess...
#  logstash_tag: The tag for this logstash instance
#  message_queue_threshold: The amount of messages in the queue at which point logstash should back off, to prevent memory issues. Defaults to 3000000 (needs to be an integer)
#  filters: A string that contains a full filter config for logstash
#  extra_inputs: A string that will be added to the input section of the logstash config
#
# Depends:
#  gen_logstash
#  kbp_redis
#  kbp_ssl
#
class kbp_logstash::server::receiver ($redis_addresses, $key_location, $external_ip=$external_ipaddress, $internal_ip=$ipaddress_eth1, $lumberjack_port=6782, $logstash_tag=false, $message_queue_threshold=3000000) {
  include kbp_logstash::server
  class {
    'gen_logstash':;
    'kbp_redis::server':
      bind_address => $internal_ip,
      appendonly   => true,
      redis_tag    => $logstash_tag;
    'kbp_redis::client':
      saddr        => $internal_ip,
      redis_tag    => $logstash_tag;
  }

  kbp_logstash::server::filter { 'collectd-memcached':; }

  kbp_logstash::server::input { 'lumberjack':
    content => template('kbp_logstash/receiver_lumberjack');
  }

  kbp_logstash::server::output { 'redis':
    content => template('kbp_logstash/receiver_redis');
  }

  kbp_ssl::keys { $key_location:
    owner   => 'logstash',
    require => Package['logstash'];
  }

  setfacl { "Allow logstash read access to /etc/ssl/private":
    dir     => '/etc/ssl/private',
    recurse => false,
    acl     => 'user:logstash:--x',
    require => Package['logstash'];
  }

  kbp_riemann::client { 'logstash':; }

  # Add munin check
  gen_munin::client::plugin { 'check_redis_logstash':
    script      => 'check_redis_logstash.py',
    script_path => "/usr/share/munin/plugins/kumina";
  }

  gen_munin::client::plugin::config { 'check_redis_logstash':
    section => 'check_redis_logstash',
    content => "env.host ${ipaddress_eth1}\n";
  }

  $logstash_ferm_tag = $logstash_tag ? {
    false   => "logstash_client",
    default => "logstash_client_${logstash_tag}",
  }

  # Import the firewall rules exported by clients
  Kbp_ferm::Rule <<| tag == $logstash_ferm_tag |>>
}

#
# Class kbp_logstash::server::processor
#
# Actions:
#  Set up Logstash and elasticsearch. These machines get stuff from redis, filter it and send it on to elasticsearch
#
# Parameters:
#  redis_addresses: An array of IP addresses where the redis-servers live
#  elasticsearch_cluster: The name of the ElasticSearch cluster
#  bind_address: The IP address we should listen on for ElasticSearch (and the saddr for the firewall rule for redis)
#  logstash_tag: The tag for this logstash instance
#
# Depends:
#  gen_logstash
#  kbp_redis
#  kbp_elasticsearch
#
class kbp_logstash::server::processor ($redis_addresses, $es_cluster_name, $graphite_address= false, $logstash_tag=false, $es_nodes=false, $es_opts=false, $es_min_nodes=1, $es_extra_opts=false, $es_heapsize=false, $es_overwrite_config=false, $saddr=$ipaddress_bond0, $redis_client_setup=false){
  include kbp_logstash::server
  class {
    'gen_logstash':
      workers           => 300;
    'kbp_elasticsearch':
      cluster_name      => $es_cluster_name,
      extra_opts        => $es_opts,
      nodes             => $es_nodes,
      min_nodes         => $es_min_nodes,
      heapsize          => $es_heapsize,
      overwrite_config  => $es_overwrite_config,
      elasticsearch_tag => $logstash_tag;
  }

  if $redis_client_setup {
    class { 'kbp_redis::client':
      saddr             => $saddr,
      redis_tag         => $logstash_tag;
    }
  }

  kbp_logstash::server::input { "redis":
    content => template('kbp_logstash/processor_redis.conf');
  }

  kbp_logstash::server::filter { ['all', 'syslog','apache', 'fail2ban', 'collectd']:; }

  kbp_logstash::server::output { 'elasticsearch':
     content => template('kbp_logstash/processor_elasticsearch.conf');
  }

  if $graphite_address {
    include kbp_graphite::client
    kbp_logstash::server::output { 'graphite':
     content => template('kbp_logstash/processor_graphite.conf');
    }
  }

  $logstash_ferm_tag = $logstash_tag ? {
      false   => "${environment}_${dcenv}_logstash",
      default => "${environment}_${dcenv}_logstash_${logstash_tag}",
  }

  # Pull the rules from the other nodes in.
  Kbp_ferm::Rule <<| tag == $logstash_ferm_tag |>>

  # head is pretty nice ES plugin for quick searches etc.
  kbp_elasticsearch::plugin {
    'mobz/elasticsearch-head':
      install_name => 'head';
    'royrusso/elasticsearch-HQ':
      install_name => 'HQ';
    'lukas-vlcek/bigdesk':
      install_name => 'bigdesk';
  }

  # Don't backup the ES datafiles (We'll figure out a better strategy later)
  kbp_backup::exclude { '/srv/elasticsearch':; }
}

define kbp_logstash::server::input ($content){
  file { "/etc/logstash/conf.d/2-${name}.conf":
    content => $content ? {
      false   => template("kbp_logstash/inputs/${name}"),
      default => $content,
    },
    notify  => Exec['restart-logstash'],
    require => Package['logstash'];
  }
}

define kbp_logstash::server::output ($content){
  file { "/etc/logstash/conf.d/8-${name}.conf":
    content => $content ? {
      false   => template("kbp_logstash/outputs/${name}"),
      default => $content,
    },
    notify  => Exec['restart-logstash'],
    require => Package['logstash'];
  }
}

define kbp_logstash::server::filter ($content=false){
  file { "/etc/logstash/conf.d/5-${name}.conf":
    content => $content ? {
      false   => template("kbp_logstash/filters/${name}"),
      default => $content,
    },
    notify  => Exec['restart-logstash'],
    require => Package['logstash'];
  }
}

class kbp_logstash::server {
  kbp_icinga::proc_status { 'logstash':
    sms => false;
  }

  file {
    '/etc/logstash/conf.d/1-start-input.conf':
      content => "input {\n",
      require => File['/etc/logstash/conf.d'];
    '/etc/logstash/conf.d/3-end-input.conf':
      content => "}\n",
      require => File['/etc/logstash/conf.d'];
    '/etc/logstash/conf.d/4-start-filter.conf':
      content => "filter {\n",
      require => File['/etc/logstash/conf.d'];
    '/etc/logstash/conf.d/6-end-filter.conf':
      content => "}\n",
      require => File['/etc/logstash/conf.d'];
    '/etc/logstash/conf.d/7-start-output.conf':
      content => "output {\n",
      require => File['/etc/logstash/conf.d'];
    '/etc/logstash/conf.d/9-end-output.conf':
      content => "}\n",
      require => File['/etc/logstash/conf.d'];
  }
}

#
# Class kbp_logstash::client
#
# Actions:
#  Set up Lumberjack
#
# Parameters:
#  servers: An array of IP addresses where the lumberjack receivers are.
#  saddr: The IP address this server will be connecting from
#  lumberjack_port: The port lumberjack listens on
#  ca_cert: The name of the ca certificate
#  logstash_tag: The tag for this logstash instance
#
# Depends:
#  gen_logstash
#  kbp_redis
#  kbp_elasticsearch
#
class kbp_logstash::client ($servers, $saddr=$source_ipaddress, $lumberjack_port=6782, $ca_cert="kumina", $logstash_tag=false) {
  if $architecture in ['amd64'] {
    include "kbp_ssl::intermediate::${ca_cert}"

    # the translate_names template takes $intermediate and translates it to the filename
    $intermediate = $ca_cert

    class { 'gen_logstash::lumberjack':
      servers => $servers,
      require => Class["kbp_ssl::intermediate::${ca_cert}"],
      sslca   => template("kbp_ssl/translate_names.erb");
    }

    kbp_icinga::proc_status { 'lumberjack':
      customer_notify => false,
      sms             => false;
    }

    Service <| title == 'lumberjack' |> {
      require +> File['/etc/default/lumberjack'],
    }

    file {
      '/etc/default/lumberjack':
        content => 'DAEMON_ARGS="-config /etc/lumberjack.conf -spool-size 1024"',
        notify  => Service['lumberjack'],
        require => Package['lumberjack'];
      # Replace the prerm... because I has made a booboo
      '/var/lib/dpkg/info/lumberjack.prerm':
        content => template('kbp_logstash/lumberjack.prerm'),
        mode    => 755;
    }

    $logstash_ferm_tag = $logstash_tag ? {
      false =>   "logstash_client",
      default => "logstash_client_${logstash_tag}",
    }

    kbp_ferm::rule { "logstash access":
      saddr    => $saddr,
      dport    => $lumberjack_port,
      proto    => 'tcp',
      exported => true,
      action   => 'ACCEPT',
      ferm_tag => $logstash_ferm_tag;
    }

    gen_apt::preference { 'lumberjack': version => '0.3.1*'; }
  } else {
    notify { "No lumberjack packages yet for ${architecture}.":; }
  }
}

# Class: kbp_logstash::client::disable
#  Action: Remove the lumberjack client from servers and it's associated config.
class kbp_logstash::client::disable {
  package { 'lumberjack':
    ensure => purged,
  }

  file { ['/etc/default/lumberjack','/etc/init.d/lumberjack','/etc/lumberjack.conf']:
    ensure => absent,
  }
}
