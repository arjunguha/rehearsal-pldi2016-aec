# From https://github.com/nelmos/puppet/tree/master/logstash
# Removed multiple sources on one file.

$osfamily = "Debian"
include logstash

## config.pp

# class "conf" provide configuration file for logstash


class logstash::conf {

  # Search base & individual configuration files
  # Restart logstash if necessary

  file {'/etc/logstash/conf.d/logstash_base.conf':
    ensure => present,
    source =>'puppet:///logstash/conf.d/logstash_base.conf',
    owner => root,
    group => root,
    mode => '0644',
    notify => Service['logstash'],
    require => File['/etc/logstash/conf.d']
  }
}


## init.pp

# class "logstash" initialize installation of all components needed to run logstash 

class logstash {

  include logstash::install
  include logstash::service
  include logstash::conf
}

## install.pp

# class "logstash" ensure installation of logstash

class logstash::install {
  
  # contain logstash binary name
  # Change value by your logstash version
  $logstash_binary = 'logstash-1.1.1-monolithic.jar'

  # Array containing a list of logstash directories
  $directories = ['/etc/logstash', '/etc/logstash/conf.d', '/usr/local/logstash', '/var/log/logstash', '/etc/init.d', '/etc/logrotate.d']

  # If not exist, make directories of $directories
  file { $directories:
    ensure => directory,
    owner => root,
    group => root,
    mode => '0644',
  }

  File['/etc/logstash'] -> File['/etc/logstash/conf.d']

  # If not exist, deploy run script
  file { '/usr/bin/logstashd':
    ensure => present,
    source => 'puppet:///modules/logstash/logstashd',
    owner => root,
    group => root,
    mode => '0755',
  }

  # If not exist, deploy init script corresponding has $osfamily return
  file { '/etc/init.d/logstash':
    ensure => present,
    source => "puppet:///modules/logstash/logstash_init_${osfamily}",
    owner => root,
    group => root,
    mode => '0755',
    require => File['/etc/init.d']
  }

  # If not exist, deploy logstash binary
  file { '/usr/local/logstash/logstash.jar':
    ensure => present,
    source => "puppet:///modules/logstash/${logstash_binary}",
    owner => root,
    group => root,
    mode => '0755',
    require => File['/usr/local/logstash']
  }

  # If not exist, deploy logrotate configuration file
  file { '/etc/logrotate.d/logstash_rotate':
    ensure => present,
    source => 'puppet:///modules/logstash/logstash_rotate',
    owner => root,
    group => root,
    mode => '0644',
    require => File['/etc/logrotate.d']
  }

  # If not exist, deploy logstash.log file
  file { '/var/log/logstash/logstash.log':
    ensure => present,
    owner => root,
    group => root,
    mode => '0664',
    require => File['/var/log/logstash'],
  }
}

## service.pp

# class "service" ensures that logstash is started

class logstash::service {

  service {"logstash":
    ensure => running,
    enable => true,
    hasstatus => true,
    hasrestart => true,
    subscribe => [File["/usr/local/logstash/logstash.jar"], File["/usr/bin/logstashd"]],
    require => File["/etc/init.d/logstash"],
  }
}

