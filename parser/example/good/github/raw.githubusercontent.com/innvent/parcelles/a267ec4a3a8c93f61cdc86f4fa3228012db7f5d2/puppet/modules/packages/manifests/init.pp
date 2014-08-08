class packages {
  @package {
    [ 'build-essential',
      'curl',
      'git',
      'htop',
      'ntp',
      'python-software-properties',
      'tmux',
      'tree',
      'unattended-upgrades',
      'unzip',
      'vim'
    ]: ensure => present
  }
}
