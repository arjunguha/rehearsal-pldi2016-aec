# The aegir slave definition.
class aegir::slave(
  $skip_apache = false
  ){
  package { 'mysql-client':
    ensure => installed,
  }

  # The aegir user and group. These will be used by the management server.
  group { 'aegir':
    ensure => present
  }
  user { 'aegir':
    ensure => 'present',
    comment => 'An aegir user',
    home => '/var/aegir',
    shell  => '/bin/bash',
    groups => 'www-data',
  }

  file { '/var/aegir':
    ensure => directory,
    require => User['aegir'],
    owner => 'aegir',
    mode => 755,
  }
  # This is where we put the web directory.
  file { '/srv/www':
    ensure => directory,
    require => User['aegir'],
    owner => 'aegir',
    mode => 755,
  }
  file { '/var/aegir/.drush':
    ensure => directory,
    require => User['aegir'],
    owner => 'aegir',
    mode => 755,
  }
  file { '/var/aegir/.ssh':
    ensure => directory,
    owner => 'aegir'
  }
  # Aegir needs to be able to restart Apache.
  file { '/etc/sudoers.d/aegir':
    ensure => present,
    owner => 'root',
    group => 'root',
    mode => '0440',
    require => User['aegir'],
    source => 'puppet:///modules/aegir/sudoer'
  }
  # Let the management server log in.
  file { '/var/aegir/.ssh/authorized_keys':
    ensure => file,
    owner => 'aegir',
    group => 'aegir',
    mode => '0440',
    source => 'puppet:///modules/aegir/keys/deploy.pub'
  }

  if ! $skip_apache {
    file { '/etc/apache2/conf.d/aegir.conf':
      ensure => link,
      target => '/var/aegir/config/apache.conf'
    }
  }
  Package { require => Exec['apt-get update'] }
}
