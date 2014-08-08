group { 'puppet': ensure => present }
Exec { path => [ '/bin/', '/sbin/', '/usr/bin/', '/usr/sbin/' ] }

$server_values = hiera('server', false)

ensure_packages( $server_values['packages'] )

class {'apt':
  always_apt_update => false,
}

apt::ppa { 'ppa:ondrej/php5-oldstable': }

class { 'rvm': version => '1.25.7' }

rvm::system_user { vagrant: }

class { 'nginx': }

$nginx = hiera('nginx', false)

class { 'php':
  package             => 'php5-fpm',
  service             => 'php5-fpm',
  service_autorestart => false,
  config_file         => '/etc/php5/fpm/php.ini',
  module_prefix       => '',
  require             => Class["apt"],
}

php::module {
  [
    $nginx['phpmodules']
  ]:
  notify  => Service["php5-fpm"]
}

service { 'php5-fpm':
  ensure     => running,
  enable     => true,
  hasrestart => true,
  hasstatus  => true,
  require    => Package['php5-fpm'],
}

class { 'php::devel':
  require => Class['php'],
}

class { 'php::pear':
  require => Class['php'],
}

class { 'xdebug':
  service => 'nginx',
}

class { 'composer':
  require => Package['php5-fpm', 'curl'],
}

class { '::mysql::server':
  root_password => 'drupaldev'
}

php::pear::module { 'drush-6.2.0.0':
  repository  => 'pear.drush.org',
  use_package => 'no',
}

php::pear::module { 'Console_Table':
  use_package => 'no',
}

php::ini { 'php.ini':
  value => $nginx['phpini'],
  require => Package["php5-cli"]
}

class { 'mailcatcher': }

#class { 'xhprof': }

if $site_values == undef {
  $site_values = hiera('sites', false)
}

if count($site_values['vhosts']) > 0 {
  create_resources(nginx_vhost, $site_values['vhosts'])
}

if is_hash($site_values['databases']) and count($site_values['databases']) > 0 {
  create_resources(mysql_db, $site_values['databases'])
}

define nginx_vhost (
  $server_name,
  $server_aliases = [],
  $www_root,
  $listen_port,
  $index_files,
  $envvars = [],
  ){
  $merged_server_name = concat([$server_name], $server_aliases)

  if is_array($index_files) and count($index_files) > 0 {
    $try_files = $index_files[count($index_files) - 1]
  } else {
    $try_files = 'index.php'
  }

  nginx::resource::vhost { $server_name:
    server_name => $merged_server_name,
    www_root    => $www_root,
    listen_port => $listen_port,
    index_files => $index_files,
    try_files   => ['$uri', '$uri/', "/${try_files}?\$args"],
  }

  nginx::resource::location { "${server_name}-php":
    ensure              => present,
    vhost               => $server_name,
    location            => '~ \.php$',
    proxy               => undef,
    try_files           => ['$uri', '$uri/', "/${try_files}?\$args"],
    www_root            => $www_root,
    location_cfg_append => {
      'fastcgi_split_path_info' => '^(.+\.php)(/.+)$',
      'fastcgi_param'           => 'PATH_INFO $fastcgi_path_info',
      'fastcgi_param '           => 'PATH_TRANSLATED $document_root$fastcgi_path_info',
      'fastcgi_param  '           => 'SCRIPT_FILENAME $document_root$fastcgi_script_name',
      'fastcgi_pass'            => 'unix:/var/run/php5-fpm.sock',
      'fastcgi_index'           => 'index.php',
      'include'                 => 'fastcgi_params'
    },
    notify              => Class['nginx::service'],
  }

  file { $www_root:
    ensure => "directory",
  }
}

define mysql_db (
  $user,
  $password,
  $host,
  $grant    = [],
  $sql_file = false
  ) {
    if $name == '' or $password == '' or $host == '' {
    fail( 'MySQL DB requires that name, password and host be set. Please check your settings!' )
  }

  mysql::db { $name:
    user     => $user,
    password => $password,
    host     => $host,
    grant    => $grant,
    sql      => $sql_file,
  }
}

class { solr:
  cores => [ 'development' ]
}

class { 'automysqlbackup':
  backup_dir           => '/home/vagrant/db'
}
