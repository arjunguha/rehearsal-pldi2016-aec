class puppet::accounts {

  group { puppet: ensure => present }

  user { puppet:
    ensure => present,
    gid => 'puppet',
    require => Group[puppet],
  }

}
