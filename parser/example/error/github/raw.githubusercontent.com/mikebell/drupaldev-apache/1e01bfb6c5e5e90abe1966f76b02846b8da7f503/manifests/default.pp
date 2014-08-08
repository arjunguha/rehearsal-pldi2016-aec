import 'devsites.pp'

group { 'puppet': ensure => present }
Exec { path => [ '/bin/', '/sbin/', '/usr/bin/', '/usr/sbin/' ] }

class {'apt':
  always_apt_update => true,
}

Class['::apt::update'] -> Package <|
    title != 'python-software-properties'
and title != 'software-properties-common'
|>

apt::ppa { "ppa:rip84/php5": }

package { [
    'build-essential',
    'vim',
    'curl',
    'git-core',
    'wget',
    'zsh',
    'htop',
    'memcached',
  ]:
  ensure  => 'installed',
}

class { 'apache': }

apache::dotconf { 'custom':
  content => 'EnableSendfile Off',
}

apache::module { 'rewrite': }

class { 'php':
  service             => 'apache',
  service_autorestart => false,
  module_prefix       => '',
}

php::module {
  [
    'php5-mysql',
    'php5-cli',
    'php5-curl',
    'php5-intl',
    'php5-mcrypt',
    'php5-gd',
    'php-apc',
    'php5-memcached'
  ]:
}

class { 'php::devel':
  require => Class['php'],
}

class { 'php::pear':
  require => Class['php'],
}

class { 'xdebug':
  service => 'apache',
}

class { 'composer':
  require => Package['php5', 'curl'],
}

puphpet::ini { 'xdebug':
  value   => [
    'xdebug.default_enable = 1',
    'xdebug.remote_autostart = 0',
    'xdebug.remote_connect_back = 1',
    'xdebug.remote_enable = 1',
    'xdebug.remote_handler = "dbgp"',
    'xdebug.remote_port = 9000'
  ],
  ini     => '/etc/php5/conf.d/zzz_xdebug.ini',
  notify  => Service['apache'],
  require => Class['php'],
}

puphpet::ini { 'php':
  value   => [
    'date.timezone = "Europe/London"',
    'sendmail_path = "/usr/bin/env /usr/local/bin/catchmail"'
  ],
  ini     => '/etc/php5/conf.d/zzz_php.ini',
  notify  => Service['apache'],
  require => Class['php'],
}

puphpet::ini { 'custom':
  value   => [
    'display_errors = On',
    'error_reporting = -1'
  ],
  ini     => '/etc/php5/conf.d/zzz_custom.ini',
  notify  => Service['apache'],
  require => Class['php'],
}

class { 'mysql::server':
  config_hash   => { 'root_password' => 'drupaldev' }
}

php::pear::module { 'drush-6.0.0RC4':
  repository  => 'pear.drush.org',
  use_package => 'no',
}

php::pear::module { 'Console_Table':
  use_package => 'no',
}

class { 'ruby':
  gems_version  => 'latest'
}

class { 'mailcatcher': }
