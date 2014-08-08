# Class to manage the /etc/login.conf file on FreeBSD.
class freebsd::login (
  $default = [
    'passwd_format=sha512',
    'copyrighta=/etc/COPYRIGHT',
    'welcome=/etc/motd',
    'setenv=MAIL=/var/mail/$,BLOCKSIZE=K',
    'path=/sbin /bin /usr/sbin /usr/bin /usr/games /usr/local/sbin /usr/local/bin ~/bin',
    'nologin=/var/run/nologin',
    'cputime=unlimited',
    'datasize=unlimited',
    'stacksize=unlimited',
    'memorylocked=unlimited',
    'memoryuse=unlimited',
    'filesize=unlimited',
    'coredumpsize=unlimited',
    'openfiles=unlimited',
    'maxproc=unlimited',
    'sbsize=unlimited',
    'vmemoryuse=unlimited',
    'swapuse=unlimited',
    'pseudoterminals=unlimited',
    'priority=0',
    'ignoretime=@',
    'umask=022'
  ]
) {

  file { '/etc/login.conf':
    path    => '/etc/login.conf',
    owner   => 'root',
    group   => '0',
    mode    => '0644',
    content => template('freebsd/etc/login.conf.erb'),
    notify  => Exec['update_login_database'],
  }

  exec{ 'update_login_database':
    command     => '/usr/bin/cap_mkdb /etc/login.conf',
    refreshonly => true,
  }
}
