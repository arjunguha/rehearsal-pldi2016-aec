# From https://github.com/mjhas/amavis
# Replaced an exec that echoed a string with a notify resource.

include amavis::config

## config.pp

class amavis::config(
  $bypass_virus_checks_maps =undef,
  $bypass_spam_checks_maps  =undef,
  $final_virus_destiny      =undef,
  $final_banned_destiny     =undef,
  $final_spam_destiny       =undef,
  $final_bad_header_destiny =undef,
) {
  include amavis
  file { '/etc/amavis/conf.d/50-user':
    ensure  => present,
    content => template('amavis/50-user'),
    notify  => Service['amavis'],
    require => Notify['amavis'],
  }
  file { '/etc/amavis/conf.d/15-content_filter_mode':
    ensure  => present,
    content => template('amavis/15-content_filter_mode'),
    require => Notify['amavis'],
    notify  => Service['amavis'],
  }
}

## init.pp

class amavis(
  $spamassassin=true
) {
  package{ 'amavisd-new':
    ensure => latest,
    alias  => 'amavis',
    before => Notify['amavis'],
  }
  if $spamassassin {
    package{ 'spamassassin':
      ensure  => latest,
      require => Package['amavis'],
      before  => Notify['amavis'],
    }
  }
  notify { 'amavis':
    message => "amavis packages are installed",
  }
  service { 'amavis':
    ensure  => running,
    require => Notify['amavis'],
  }
}

