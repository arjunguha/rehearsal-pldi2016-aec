# Author: Kumina bv <support@kumina.nl>

class kbp_loadbalancer ($failover=true, $haproxy_loglevel='warning', $loadbalancer_tag="${environment}_${custenv}", $heartbeat_dev='eth0', $heartbeat_ip=$ipaddress_eth0, $heartbeat_initdead='60') {
  class { 'kbp_haproxy':
    haproxy_loglevel => $haproxy_loglevel;
  }

  if $failover {
    include kbp_pacemaker
    class { 'kbp_heartbeat':
      node_dev      => $heartbeat_dev,
      node_ip       => $heartbeat_ip,
      initdead      => $heartbeat_initdead,
      heartbeat_tag => $loadbalancer_tag;
    }
  }

  Kbp_loadbalancer::Ip <<| tag == "loadbalancer_${loadbalancer_tag}" |>>
  Kbp_haproxy::Site::Add_server <<| tag == "haproxy_${loadbalancer_tag}" |>>
}

define kbp_loadbalancer::ip ($exported=true, $failover=true, $site, $loadbalancer_tag="${environment}_${custenv}", $location=false, $serverip=$ipaddress, $serverport=80, $cookie=false, $httpcheck_uri=false,
    $httpcheck_port=$serverport, $balance='roundrobin', $timeout_connect='10s', $timeout_server_client='10s', $timeout_http_request='10s', $tcp_sslport=false, $monitoring_ha=false,
    $monitoring_hostname=$site, $monitoring_status='200', $monitoring_url=false, $monitoring_max_check_attempts=false, $monitoring_response=false, $monitoring_proxy=false, $nic='eth0',
    $monitoring_address=false, $sslport=false, $httpcheck_interval=false, $httpcheck_fall=false, $httpcheck_rise=false, $backupserver=false, $monitor_site=true, $export_done=false, $netmask=32,
    $forwardfor_except=false, $monitor_interval='10s', $monitor_timeout='20s', $httpclose=false, $timeout_server='20s', $redirect_non_ssl=false, $server_name=$fqdn, $timeout_check='10s',
    $redirect_non_ssl_monitoring_statuscode=301, $redir=false, $remove_external_forwarded_for=true, $orig_cust=$environment, $orig_env=$custenv, $cert=false, $key=false, $wildcard=false, $intermediate=false,
    $intermediate_file=false) {
  $real_name = regsubst($name, '(.*);.*', '\1')
  $server    = regsubst($name, '.*;(.*)', '\1')
  $ip        = regsubst($real_name, '(.*)_.*', '\1')
  $temp_port = regsubst($real_name, '.*_(.*)', '\1')
  $port      = $temp_port ? {
    $real_name => 80,
    default    => $temp_port,
  }

  if $redirect_non_ssl {
    if ! $sslport {
      fail("kbp_loadbalancer::ip ${name}: \$redirect_non_ssl only makes sense to be true when \$sslport is also set as it only works for when stunnel is used, otherwise the redirect can be done in the normal way on the webservers.")
    } elsif ! $export_done {
      kbp_apache::vhost_addition { "${site}/${site}_non_ssl_redirect":
        content => "RewriteEngine On\nRewriteCond %{HTTP:X-SSL} !^On$\nRewriteRule (.*) https://${site}\$1 [QSA,NE,R=301,L]\n";
      }

      Kbp_icinga::Site <| title == $site |> {
        statuscode => $redirect_non_ssl_monitoring_statuscode,
      }
    }
  }
  if ! $exported {
    $provider  = $dcenv ? {
      'hetzner' => 'ocf:kumina:hetzner-failover-ip',
      default   => 'ocf:heartbeat:IPaddr2',
    }

    if $failover and ! defined(Kbp_pacemaker::Primitive["${site}:${ip}"]) {
      kbp_pacemaker::primitive { "${site}:${ip}":
        provider         => $provider,
        start_timeout    => '300s',
        monitor_interval => $monitor_interval,
        monitor_timeout  => $monitor_timeout,
        params           => $provider ? {
          'ocf:heartbeat:IPaddr2'          => "ip=\"${ip}\" cidr_netmask=\"${netmask}\" nic=\"${nic}\" lvs_support=\"true\"",
          'ocf:kumina:hetzner-failover-ip' => "ip=\"${ip}\" script=\"/usr/local/sbin/parse-hetzner-json.py\"",
        },
        location         => $location;
      }
    }

    if ! defined(Kbp_haproxy::Site["${ip}_${port}"]) {
      kbp_haproxy::site { "${ip}_${port}":
        cookie                                 => $cookie,
        site                                   => $site,
        monitor_site                           => $monitor_site,
        monitoring_ha                          => $monitoring_ha,
        max_check_attempts                     => $max_check_attempts,
        monitoring_status                      => $monitoring_status,
        monitoring_url                         => $monitoring_url,
        monitoring_response                    => $monitoring_response,
        monitoring_address                     => $monitoring_address,
        monitoring_hostname                    => $monitoring_hostname,
        balance                                => $balance,
        timeout_connect                        => $timeout_connect,
        timeout_server_client                  => $timeout_server_client,
        timeout_http_request                   => $timeout_http_request,
        timeout_check                          => $timeout_check,
        tcp_sslport                            => $tcp_sslport,
        monitoring_proxy                       => $monitoring_proxy,
        httpcheck_uri                          => $httpcheck_uri,
        forwardfor_except                      => $forwardfor_except,
        httpclose                              => $httpclose,
        timeout_server                         => $timeout_server,
        sslport                                => $sslport,
        remove_external_forwarded_for          => $remove_external_forwarded_for,
        redirect_non_ssl_monitoring_statuscode => $redirect_non_ssl_monitoring_statuscode,
        redirect_non_ssl                       => $redirect_non_ssl,
        orig_cust                              => $orig_cust,
        orig_env                               => $orig_env;
      }
    }

    if $export_done {
      kbp_haproxy::site::add_server { "${ip}_${port};${server}":
        cookie             => $cookie,
        serverport         => $serverport,
        serverip           => $serverip,
        httpcheck_uri      => $httpcheck_uri,
        httpcheck_port     => $httpcheck_port,
        httpcheck_interval => $httpcheck_interval,
        httpcheck_fall     => $httpcheck_fall,
        httpcheck_rise     => $httpcheck_rise,
        tcp_sslport        => $tcp_sslport,
        backupserver       => $backupserver,
        redir              => $redir;
      }
    } else {
      @@kbp_haproxy::site::add_server { "${ip}_${port};${server_name}":
        cookie             => $cookie,
        serverport         => $serverport,
        serverip           => $serverip,
        httpcheck_uri      => $httpcheck_uri,
        httpcheck_port     => $httpcheck_port,
        httpcheck_interval => $httpcheck_interval,
        httpcheck_fall     => $httpcheck_fall,
        httpcheck_rise     => $httpcheck_rise,
        tcp_sslport        => $tcp_sslport,
        backupserver       => $backupserver,
        tag                => "haproxy_${loadbalancer_tag}",
        redir              => $redir;
      }
    }

    if $sslport {
      if ! defined(Kbp_stunnel::Site[$site]) {
        kbp_stunnel::site { $site:
          ip                => $ip,
          port              => $sslport,
          cert              => $cert,
          key               => $key,
          wildcard          => $wildcard,
          intermediate      => $intermediate,
          intermediate_file => $intermediate_file;
        }
      }
    }
  } else {
    @@kbp_loadbalancer::ip { "${name};${server_name}":
      exported                               => false,
      export_done                            => true,
      site                                   => $site,
      location                               => $location,
      serverip                               => $serverip,
      serverport                             => $serverport,
      httpcheck_uri                          => $httpcheck_uri,
      httpcheck_port                         => $httpcheck_port,
      httpcheck_interval                     => $httpcheck_interval,
      httpcheck_fall                         => $httpcheck_fall,
      httpcheck_rise                         => $httpcheck_rise,
      cookie                                 => $cookie,
      balance                                => $balance,
      timeout_connect                        => $timeout_connect,
      timeout_server_client                  => $timeout_server_client,
      timeout_http_request                   => $timeout_http_request,
      timeout_check                          => $timeout_check,
      tcp_sslport                            => $tcp_sslport,
      monitoring_max_check_attempts          => $monitoring_max_check_attempts,
      monitoring_ha                          => $monitoring_ha,
      monitoring_hostname                    => $monitoring_hostname,
      monitoring_status                      => $monitoring_status,
      monitoring_response                    => $monitoring_response,
      monitoring_url                         => $monitoring_url,
      monitoring_proxy                       => $monitoring_proxy,
      monitoring_address                     => $monitoring_address,
      monitor_site                           => $monitor_site,
      nic                                    => $nic,
      sslport                                => $sslport,
      redirect_non_ssl                       => $redirect_non_ssl,
      redirect_non_ssl_monitoring_statuscode => $redirect_non_ssl_monitoring_statuscode,
      remove_external_forwarded_for          => $remove_external_forwarded_for,
      backupserver                           => $backupserver,
      forwardfor_except                      => $forwardfor_except,
      monitor_timeout                        => $monitor_timeout,
      monitor_interval                       => $monitor_interval,
      httpclose                              => $httpclose,
      timeout_server                         => $timeout_server,
      tag                                    => "loadbalancer_${loadbalancer_tag}",
      redir                                  => $redir,
      cert                                   => $cert,
      key                                    => $key,
      wildcard                               => $wildcard,
      intermediate                           => $intermediate,
      intermediate_file                      => $intermediate_file,
      orig_cust                              => $orig_cust,
      orig_env                               => $orig_env;
    }
  }
}
