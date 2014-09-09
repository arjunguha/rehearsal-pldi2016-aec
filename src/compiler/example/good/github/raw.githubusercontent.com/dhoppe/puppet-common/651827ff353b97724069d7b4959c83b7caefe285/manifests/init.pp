class common inherits common::params {
  file { [
    '/etc/group',
    '/etc/passwd' ]:
    owner => 'root',
    group => 'root',
    mode  => '0644',
  }

  file { '/etc/shadow':
    owner => 'root',
    group => 'shadow',
    mode  => '0640',
  }

  if $::virtual == 'physical' {
    file { '/etc/default/smartmontools':
      owner   => 'root',
      group   => 'root',
      mode    => '0644',
      alias   => 'smartmontools',
      source  => 'puppet:///modules/common/common/etc/default/smartmontools',
      notify  => Service['smartmontools'],
      require => Package['smartmontools'],
    }

    service { 'smartmontools':
      ensure     => running,
      enable     => true,
      hasrestart => true,
      hasstatus  => false,
      require    => [
        File['smartmontools'],
        Package['smartmontools']
      ],
    }

    package { [
      'bonnie++',
      'memtest86+',
      'smartmontools' ]:
      ensure => present,
    }
  }

  package { [
    'acpid',
    'colordiff',
    'dcfldd',
    'debian-goodies',
    'deborphan',
    'dstat',
    'ethtool',
    'htop',
    'ifstat',
    'iftop',
    'iotop',
    'ipcalc',
    'iperf',
    'lsb-release',
    'molly-guard',
    'mtr-tiny',
    'nmap',
    'parted',
    'psmisc',
    'pwgen',
    'rsync',
    'sysstat',
    'tcpdump',
    'tmux',
    'tree',
    'unrar',
    'unzip',
    'zsh' ]:
    ensure => present,
  }
}
