class gitlab::service {

  file { '/etc/init.d/gitlab':
    ensure  => present,
    mode    => '0755',
    owner   => 'root',
    group   => 'root',
    content => template('gitlab/gitlab.erb'),
    notify  => Service['gitlab'],
  }

  service { 'gitlab':
    ensure     => running,
    enable     => true,
    hasrestart => true,
    hasstatus  => false,
    require    => File['/etc/init.d/gitlab'];
  }

}
