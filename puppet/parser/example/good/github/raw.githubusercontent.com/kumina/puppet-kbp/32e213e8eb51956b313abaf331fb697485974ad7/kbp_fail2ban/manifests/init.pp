# Author: Kumina bv <support@kumina.nl>

# Class: kbp_fail2ban
#
# Actions:
#  Setup Fail2Ban.
#
# Depends:
#  gen_fail2ban
#
class kbp_fail2ban ($ignoreip='', $email=false, $bantime='7200') {
  # We never want to block the Kumina office or mon1.kumina.nl, mon2.kumina.nl, munin2.kumina.nl
  $real_ignoreip = "127.0.0.0/8 10.0.0.0/8 192.168.0.0/16 172.16.0.0/12 78.108.143.14/32 212.153.88.197/32 31.177.34.95/32 212.153.70.98/32 212.153.70.150/32 212.153.88.207/32 212.153.70.165/32 ${ignoreip}"

  class { 'gen_fail2ban':
    ignoreip  => $real_ignoreip,
    email     => $email,
    banaction => 'iptables-input-and-forward',
    bantime   => $bantime;
  }

  # All our servers run ssh, protect it by default.
  include gen_fail2ban::ssh

  # Trend fail2ban
  include kbp_munin::client::fail2ban

  # Ship the logs
  if defined(Class['kbp_logstash::client']) and $architecture in ['amd64'] {
    gen_logstash::lumberjack::files { "Fail2ban logs":
      file_type  => "fail2ban",
      files      => "/var/log/fail2ban.log";
    }
  }

  # We do not want to get emails when services are started.
  file {
    '/etc/fail2ban/action.d/sendmail-whois-lines.conf':
      content => template('kbp_fail2ban/action.d/sendmail-whois-lines.conf'),
      require => Package['fail2ban'],
      notify  => Exec['reload-fail2ban'];
    '/etc/fail2ban/action.d/iptables-multiport-input-and-forward.conf':
      content => template('kbp_fail2ban/action.d/iptables-multiport-input-and-forward.conf'),
      require => Package['fail2ban'],
      notify  => Exec['reload-fail2ban'];
    '/etc/fail2ban/action.d/iptables-input-and-forward.conf':
      content => template('kbp_fail2ban/action.d/iptables-input-and-forward.conf'),
      require => Package['fail2ban'],
      notify  => Exec['reload-fail2ban'];
  }

  # These are hooks that we need in ferm
  gen_ferm::hook {
    'stop fail2ban before ferm stop':
      type    => 'flush',
      command => '/etc/init.d/fail2ban stop';
    'start fail2ban after ferm start':
      type    => 'post',
      command => '/etc/init.d/fail2ban restart';
  }

  # Monitor the fail2ban-server
  kbp_icinga::service {
    "fail2ban":
      service_description => "Fail2Ban-server Status",
      check_command       => "check_fail2ban",
      nrpe                => true,
      sms                 => false;
  }

  # Setup the iptables rules in ferm for the default filters we deploy
  kbp_fail2ban::ferm_rules { 'ssh-ddos':; }
  kbp_fail2ban::ferm_rules { 'ssh': ordering => 'a'; }
}

# Class: kbp_fail2ban::postfix
#  Actions: Setup Fail2Ban settings for postfix.
class kbp_fail2ban::postfix {
  include gen_fail2ban::postfix
  kbp_fail2ban::ferm_rules { 'postfix':; }
}

# Class: kbp_fail2ban::mailrelay
#
# Actions: Setup Fail2Ban settings for mailserver we use to relay mail for multiple hosts.
#
class kbp_fail2ban::mailrelay {
  include kbp_fail2ban::postfix
  include gen_fail2ban::sasl
  kbp_fail2ban::ferm_rules { 'sasl':; }
}

# Class: kbp_fail2ban::incoming_email
#
# Actions: Setup Fail2Ban settings for a mailserver that receives incoming email.
#
class kbp_fail2ban::incoming_email {
  include kbp_fail2ban::postfix
  include gen_fail2ban::dovecot
  kbp_fail2ban::ferm_rules { 'dovecot':; }
}

# Class: kbp_fail2ban::asterisk
#  Actions: Setup fail2ban rules for asterisk.
class kbp_fail2ban::asterisk {
  include gen_fail2ban::asterisk
  kbp_fail2ban::ferm_rules { 'asterisk':; }
}

# Class: kbp_fail2ban::ferm_rules
#  Actions: Setup the ferm rules for a specific fail2ban filter.
#  Parameters:
#   name: Name of the filter, without the fail2ban prefixed.
#   prio: Priority, sometimes needed to fix sorting errors. Default to 100.
define kbp_fail2ban::ferm_rules ($prio=100, $ordering='') {
  gen_ferm::chain { "fail2ban-${name}_filter_v4":
    ordering => $ordering;
  }

  # Jump to these chains before doing anything else
  gen_ferm::rule {
    "Check fail2ban-${name} return to whence it came":
      chain  => "fail2ban-${name}",
      ordering => 'a',
      action => 'RETURN';
    "Check fail2ban-${name} from INPUT chain":
      chain  => 'INPUT',
      prio   => $prio,
      action => "jump fail2ban-${name}";
    "Check fail2ban-${name} from FORWARD chain":
      chain  => 'FORWARD',
      prio   => $prio,
      action => "jump fail2ban-${name}";
  }
}
