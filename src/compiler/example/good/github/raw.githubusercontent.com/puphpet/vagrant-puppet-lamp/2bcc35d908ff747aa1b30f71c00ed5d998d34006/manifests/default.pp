exec { 'apt-get update':
  command => 'apt-get update',
  path    => '/usr/bin/',
  timeout => 60,
  tries   => 3
}

class { 'apt':
  always_apt_update => true
}

package {
  [
    'build-essential',
    'python-software-properties',
    'puppet-lint',
    'vim',
    'curl',
    'zip'
  ]:
  ensure  => 'installed',
  require => Exec['apt-get update'],
}

file { '/home/vagrant/.bash_aliases':
  ensure => 'present',
  source => 'puppet:///modules/puphpet/dot/.bash_aliases',
}

apt::ppa { 'ppa:ondrej/php5':
  before  => Class['php']
}

git::repo { 'puphpet':
  path   => '/var/www/puphpet.dev/',
  source => 'https://github.com/jtreminio/Puphpet.git'
}

class { 'apache':
  require => Apt::Ppa['ppa:ondrej/php5'],
}

apache::dotconf { 'custom':
  content => 'EnableSendfile Off',
}

apache::module { 'rewrite': }

apache::vhost { 'puphpet':
  server_name   => 'puphpet.dev',
  serveraliases => ['www.puphpet.dev'],
  docroot       => '/var/www/puphpet.dev/web',
  port          => '80',
  priority      => '1',
  require       => Git::Repo['puphpet']
}

class { 'php':
  service => 'apache',
  require => Package['apache'],
}

php::module { 'php5-cli': }
php::module { 'php5-curl': }
php::module { 'php5-intl': }
php::module { 'php5-mcrypt': }
php::module { 'php5-mysql': }

class { 'php::pear':
  require => Class['php'],
}

class { 'php::devel':
  require => Class['php'],
}

class { 'php::composer':
  require => Package['php5', 'curl'],
}

php::composer::run { 'puphpet':
  path    => '/var/www/puphpet.dev/',
  require => Git::Repo['puphpet']
}

php::ini { 'default':
  value  => [
    'date.timezone = America/Chicago',
    'display_errors = On',
    'error_reporting = -1'
  ],
  target => 'error_reporting.ini'
}

class { 'xdebug': }

xdebug::config { 'cgi': }
xdebug::config { 'cli': }

php::pecl::module { 'xhprof':
  use_package => false,
}

apache::vhost { 'xhprof':
  server_name => 'xhprof',
  docroot     => '/var/www/xhprof/xhprof_html',
  port        => '80',
  priority    => '1',
  require     => Php::Pecl::Module['xhprof']
}
