# Author: Kumina bv <support@kumina.nl>

class kbp_postfix::mailgraph {
  include gen_base::mailgraph
}

# Class: kbp_postfix
#
# Actions:
#  Undocumented
#
# Depends:
#  Undocumented
#  gen_puppet
#
class kbp_postfix($certs=false, $relayhost=false, $mailname=false, $myhostname=false, $mynetworks=false, $mydestination=false, $mode=false,
    $mailname=$fqdn, $incoming=false, $always_bcc=false, $mysql_user=false, $mysql_pass=false, $mysql_db=false, $mysql_host=false,
    $relay_domains=false, $mydomain=$domain, $check_policy_service='inet:127.0.0.1:10023', $content_filter='lmtp-amavis:[127.0.0.1]:10024',
    $inet_protocols='all', $self_signed_certs=false) {
  include kbp_openssl::common
  include kbp_collectd::plugin::postfix
  class { 'gen_postfix':
    certs                => $certs,
    self_signed_certs    => $self_signed_certs,
    relayhost            => $relayhost,
    mydomain             => $mydomain,
    myhostname           => $myhostname,
    mynetworks           => $mynetworks,
    mydestination        => $mydestination,
    mode                 => $mode,
    always_bcc           => $always_bcc,
    mysql_user           => $mysql_user,
    mysql_pass           => $mysql_pass,
    mysql_db             => $mysql_db,
    mysql_host           => $mysql_host,
    relay_domains        => $relay_domains,
    check_policy_service => $check_policy_service,
    inet_protocols       => $inet_protocols,
    content_filter       => $content_filter;
  }
  if $mode == 'primary' {
    include gen_base::postfix_mysql
    if ! $certs {
      fail('When using primary mode for kbp_postfix, $certs must be set')
    }
  }

  gen_postfix::alias { ["root: reports+${environment}@kumina.nl","reports: reports+${environment}@kumina.nl"]:; }

  file { '/etc/mailname':
    content => $mailname ? {
      false   => "${fqdn}\n",
      default => "${mailname}\n",
    },
    notify  => Exec['reload-postfix'];
  }

  exec { "postmap blocked_domains":
    command     => "/usr/sbin/postmap /etc/postfix/blocked_domains",
    refreshonly => true;
  }

  gen_munin::client::plugin {
    ['postfix_mailqueue', 'postfix_mailstats', 'postfix_mailvolume']:;
    ['exim_mailstats']:
      ensure => absent;
  }

  kbp_icinga::proc_status { 'postfix':
    sms => false;
  }
}
