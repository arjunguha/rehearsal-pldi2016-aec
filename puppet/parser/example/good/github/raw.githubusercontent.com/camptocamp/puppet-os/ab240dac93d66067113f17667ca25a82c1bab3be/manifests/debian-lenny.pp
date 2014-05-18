class os::debian-lenny {

  include os::debian

  # Disable PC Speaker
  kmod::blacklist {'pcspkr': }

  # Get rid of the old file
  file {'/etc/modprobe.d/blacklist':
    ensure => absent,
  }

  # general config for emacs (without temporary files ~ )
  file { '/etc/emacs/site-start.d/50c2c.el':
    ensure  => present,
    mode    => '0644',
    source  => 'puppet:///modules/os/etc/emacs/site-start.d/50c2c.el',
    require => Package['emacs23-nox']
  }

  apt::pin {'c2c-mirror':
    ensure     => present,
    originator => 'c2c',
    priority   => 1001,
  }

  # fix 7376
  package {[
    'openssh-server',
    'openssh-client',
    'openssh-blacklist',
    'ssl-cert',
  ]:
    ensure => latest,
  }

  exec {'sysctl-reload':
    command     => 'sysctl -p',
    refreshonly => true,
  }

  # fixes rt#14979
  cron {'Keeps a fresh apt database':
    ensure   => present,
    command  => '/usr/bin/apt-get update -q=2',
    hour     => 4,
    minute   => fqdn_rand(60),
  }
}
