class ssh (
  $group = $ssh::params::group
) inherits ssh::params {

  validate_string(hiera('group'))

  file { '/etc/ssh/sshd_config':
    owner   => 'root',
    group   => 'root',
    mode    => '0644',
    alias   => 'sshd_config',
    source  => "puppet:///modules/ssh/${::lsbdistcodename}/etc/ssh/sshd_config",
    notify  => Service['ssh'],
    require => Package['openssh-server'],
  }

  $users_real = split($::users, ',')
  ssh::users { $users_real:
    group => $group,
  }

  file { '/root/.ssh':
    force   => true,
    purge   => true,
    recurse => true,
    owner   => 'root',
    group   => 'root',
    mode    => '0600',
    source  => [
      "puppet:///modules/ssh/common/root/.ssh/${::hostname}",
      'puppet:///modules/ssh/common/root/.ssh'
    ],
  }

  package { 'openssh-server':
    ensure => present,
  }

  service { 'ssh':
    ensure     => running,
    enable     => true,
    hasrestart => true,
    hasstatus  => true,
    require    => [
      File['sshd_config'],
      Package['openssh-server']
    ],
  }
}