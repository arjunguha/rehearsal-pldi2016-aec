$::fqdn = "foo.com" # HACK(arjun)

# From https://github.com/nfisher/SpikyIRC
# Contents were flattened by removing the usage of node.
# Drugs are baaadd m'kay. Don't do stages at home kids.
#stage { 'epel': before => Stage['main'] }
#include apache
#include collectd
#include collectd::web
#class { 'epel': stage => 'epel' }
#include ircd
include irssi
#include ssh
include users
include sudoers

# TODO: This is a pants way to manage what's run against Vagrant.
if "localhost.localdomain" != $::fqdn {
  include postfix
  include sudoers
}

class apache {
  package { 'httpd':
    ensure => latest,
  }

  service { 'httpd':
    ensure  => running,
    enable  => true,
    require => Package['httpd'],
  }

  file { 'httpd_conf':
    ensure  => file,
    path    => '/etc/httpd/conf/httpd.conf',
    owner   => 'root',
    group   => 'root',
    mode    => '0644',
    source  => 'puppet:///modules/apache/httpd.conf',
    notify  => Service['httpd'],
    require => Package['httpd'],
  }
}
class autodeploy {
  file { 'root_bin':
    ensure => directory,
    path   => '/root/bin',
    mode   => '0700',
    owner  => 'root',
    group  => 'root',
  }

  file { 'autodeploy.sh':
    ensure  => file,
    path    => '/root/bin/autodeploy.sh',
    mode    => '0700',
    owner   => 'root',
    group   => 'root',
    source  => 'puppet:///modules/autodeploy/autodeploy.sh',
    require => File['root_bin'],
  }
}
class collectd {

  package { 'collectd':
    ensure  => latest,
    require => Class['epel'],
  }

  package { 'collectd-rrdtool':
    ensure  => latest,
    require => Package['collectd'],
    notify  => Service['collectd'],
  }

  file { 'collectd_swap':
    ensure  => file,
    path    => '/etc/collectd.d/swap.conf',
    content => "LoadPlugin swap\n",
    owner   => 'root',
    group   => 'root',
    mode    => '0644',
    require => Package['collectd'],
    notify  => Service['collectd'],
  }

  service { 'collectd':
    ensure  => running,
    enable  => true,
    require => Package['collectd'],
  }
}

class collectd::web {
  # Too lazy to setup another configuration for collectd.
  package { 'collectd-web':
    ensure  => latest,
    require => Class['epel'],
  }
}

class epel {
  package { 'epel-release':
    ensure   => present,
    provider => 'rpm',
    source   => 'http://dl.fedoraproject.org/pub/epel/6/x86_64/epel-release-6-7.noarch.rpm',
  }
}

class iptables {
  service {'iptables':
    restart    => '/etc/init.d/iptables reload',
    hasstatus  => true,
  }
}
class ircd {
  package {'ircd-hybrid':
    ensure => latest,
  }

  file {'etc_ircd_conf':
    ensure  => present,
    path    => '/etc/ircd/ircd.conf',
    owner   => 'ircd',
    group   => 'ircd',
    mode    => '0640',
    source  => "puppet:///modules/ircd/ircd.conf",
    require => Package['ircd-hybrid'],
    notify  => Service['ircd'],
  }

  service {'ircd':
    ensure     => 'running',
    enable     => true,
    # Use reload so hopefully not everyone gets dropped.
    restart    => '/sbin/service ircd reload',
    hasrestart => true,
    hasstatus  => true,
    require    => Package['ircd-hybrid'],
  }
}

class irssi {
  package { 'irssi':
    ensure => latest,
  }
}
class postfix {
  service { 'postfix':
    ensure => 'stopped',
    enable => false,
  }
}
class ssh {
  package { 'openssh-server':
    ensure => latest,
    before => File['sshd_config']
  }

  service { 'sshd':
    ensure     => running,
    # Use reload instead of restart so the session is maintained
    restart    => '/sbin/service sshd reload',
    enable     => true,
    hasrestart => true,
    hasstatus  => true,
  }

  file { 'sshd_config':
    ensure => present,
    path   => '/etc/ssh/sshd_config',
    mode   => '0600',
    owner  => 'root',
    group  => 'root',
    source => 'puppet:///modules/ssh/sshd_config',
    notify => Service['sshd'],
  }
}

class sudoers {
  file { 'sudoers':
    ensure => present,
    path   => '/etc/sudoers',
    mode   => '0440',
    owner  => 'root',
    group  => 'root',
    content => "dummy sudoers content",
  }
}

class users {
  user { 'deployer':
    ensure     => present,
    managehome => true,
    groups     => 'wheel',
  }

  ssh_authorized_key { 'deployer_key':
    ensure  => present,
    key     => 'AAAAB3NzaC1yc2EAAAADAQABAAABAQDHB/a1L7iEH/SMUBukLpUpCQgZboOEvc+0RHMQZ0JMC4iaxzwoAbbDRUvv2T39NRXaojk3cgAQ9D9piN91jU9qwgVTTRs4smHs/A1yxvlsZVL879Q6pTBQpXFYMCEL9rSVQtHK27mEVht5SOoephKoTgA2icOqtbNFdWyb27v/CEE/k9sKI4igJsIbLzhjN9TYQf8LW8d9DvCuNbgXSYUK6iK/7w6hmAlHMXhCSs2LsvkjEqLSgCgUo0FRnUX76dGBpoDNKe6jryPKMlGZN5A73yOF1mpTSw33KJRXi99Uq1jQiQRfIgwHd5YSaX/Q+4xpdBaoAyh5+A45fQBGmT63',
    type    => 'rsa',
    user    => 'deployer',
    require => User['deployer'],
  }

  ssh_authorized_key { 'deployer_key2':
    ensure  => present,
    key     => 'AAAAB3NzaC1yc2EAAAADAQABAAABAQC5U2M4XmaFit2AMOtrP01im9mkmizrl7heUq8KXXN+BFYLj8GMKTQSWpfb8uB7enh8KKuqhZLQ4FXAxY+j11UTDWmSAS/TMrj30YT6ZpKvKKO8S+ossqxoYaACiS2oTVVOtwkcoaP+S3uRjmH4crIOhuYiGbzGt0XLyDv9aH2J8bVWqcWw31P5NjzTAKWNhNfxFOVdRUissUPTxndgzow2KXJ51c50zWMM97rufseznqvTOFMrcHag7QEcxe1LCKw/5RkUD8exAn336Hpcq57ipJvVb5jU6Yz21QIGuQgsJ6c07BASGGnDqQljO4NCVdR/ftszvQ56s8gUPqe/bkUx',
    type    => 'rsa',
    user    => 'deployer',
    require => User['deployer'],
  }

  ssh_authorized_key { 'nfisher_key2':
    ensure  => present,
    key     => 'AAAAB3NzaC1yc2EAAAADAQABAAABAQC5U2M4XmaFit2AMOtrP01im9mkmizrl7heUq8KXXN+BFYLj8GMKTQSWpfb8uB7enh8KKuqhZLQ4FXAxY+j11UTDWmSAS/TMrj30YT6ZpKvKKO8S+ossqxoYaACiS2oTVVOtwkcoaP+S3uRjmH4crIOhuYiGbzGt0XLyDv9aH2J8bVWqcWw31P5NjzTAKWNhNfxFOVdRUissUPTxndgzow2KXJ51c50zWMM97rufseznqvTOFMrcHag7QEcxe1LCKw/5RkUD8exAn336Hpcq57ipJvVb5jU6Yz21QIGuQgsJ6c07BASGGnDqQljO4NCVdR/ftszvQ56s8gUPqe/bkUx',
    type    => 'rsa',
    user    => 'nfisher',
    require => Users::Irc['nfisher'],
  }

  # The user used to provision the users from the bouncer app
  user { 'bouncerprovisioner':
    ensure     => present,
    managehome => true,
    groups     => 'wheel',
  }

  ssh_authorized_key { "bouncer_provisioner_key":
    ensure => present,
    key    => "AAAAB3NzaC1yc2EAAAADAQABAAABAQDLT2Z1kNmeNbfXWDGtwei4TOl/tgW8RuyEp8FVsjkoVNfqNSUOEFhyYekjh/y5TYC95i6kZrBvKIsXO9TCmQ0kxRrhLwvwMMXLAF8QTs60bote6ExRL1pSNwmYP92wUpnJ7o5zMSUH9Pm3HKeAMSQ6sLZYNZ9VKtU07/zFbQfYKVBVd1pRjr/atpJ0Z9qkiYQbzqLyQUoKCQvdastsk2VHzgXdYnErhYH0E+Bg/1MqEVUZ/VpYirRe0FiKXzdtRq1O/cYzgOHtq1rNCcr/jzOGqHD4FsCJ29Jamksk7jfNC0wvUT0uPdkO0gDm3gMU3gCVTO3BJn0kTSFNkBNm9qC7",
    type   => "rsa",
    user   => "bouncerprovisioner",
    require => User["bouncerprovisioner"]
  }

  users::irc {
    'nfisher': fullname => 'Nathan Fisher', key => 'AAAAB3NzaC1yc2EAAAADAQABAAABAQDHB/a1L7iEH/SMUBukLpUpCQgZboOEvc+0RHMQZ0JMC4iaxzwoAbbDRUvv2T39NRXaojk3cgAQ9D9piN91jU9qwgVTTRs4smHs/A1yxvlsZVL879Q6pTBQpXFYMCEL9rSVQtHK27mEVht5SOoephKoTgA2icOqtbNFdWyb27v/CEE/k9sKI4igJsIbLzhjN9TYQf8LW8d9DvCuNbgXSYUK6iK/7w6hmAlHMXhCSs2LsvkjEqLSgCgUo0FRnUX76dGBpoDNKe6jryPKMlGZN5A73yOF1mpTSw33KJRXi99Uq1jQiQRfIgwHd5YSaX/Q+4xpdBaoAyh5+A45fQBGmT63';
  }
}
define users::irc($key, $fullname, $ensure = 'present', $username = $title, $type = 'rsa') {
  if 'present' == $ensure {
    $dir_ensure  = 'directory'
    $file_ensure = 'file'
  } else {
    $dir_ensure  = 'absent'
    $file_ensure = 'absent'
  }

  user { "$username":
    ensure     => $ensure,
    comment    => $fullname,
    managehome => true,
    shell      => '/usr/bin/irssi',
    require    => Class['irssi'],
  }

  file { "${username}_irssi_dir":
    ensure  => $dir_ensure,
    path    => "/home/${username}/.irssi",
    mode    => '0755',
    owner   => $username,
    group   => $username,
    require => User[$username],
  }

  file { "${username}_irssi_config":
    ensure  => $file_ensure,
    path    => "/home/${username}/.irssi/config",
    content => template('users/irssi_config'),
    require => File["${username}_irssi_dir"],
  }

  ssh_authorized_key { "${username}_key":
    ensure  => $ensure,
    key     => $key,
    type    => $type,
    user    => $username,
    require => User[$username],
  }
}
