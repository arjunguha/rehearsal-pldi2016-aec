
$doc_root        = '/vagrant/web'
$php_modules     = [ 'imagick', 'curl', 'mysql', 'cli', 'intl', 'mcrypt', 'memcache']
$sys_packages    = [ 'build-essential', 'curl', 'vim']
$mysql_host      = 'localhost'
$mysql_db        = 'symfony'
$mysql_user      = 'symfony'
$mysql_pass      = 'password'
$pma_port        = 8000


Exec { path => [ "/bin/", "/sbin/" , "/usr/bin/", "/usr/sbin/" ] }

exec { 'apt-get update':
    command => 'apt-get update',
}

class { 'apt':
    always_apt_update => true,
}

class { 'git': }

package { ['python-software-properties']:
    ensure  => 'installed',
    require => Exec['apt-get update'],
}

package { $sys_packages:
    ensure => "installed",
    require => Exec['apt-get update'],
}
class { "apache": }

apache::module { 'rewrite': }

apache::vhost { 'default':
    docroot                  => $doc_root,
    directory                => $doc_root,
    directory_allow_override => "All",
    server_name              => false,
    priority                 => '000',
    template                 => 'vagrantee/apache/vhost.conf.erb',
}

apt::ppa { 'ppa:ondrej/php5':
    before  => Class['php'],
}

class { 'php': }

php::module { $php_modules: }

vagrantee::phpini { 'php':
    value      => ['date.timezone = "UTC"','upload_max_filesize = 8M', 'short_open_tag = 0'],
}

class { 'mysql':
    root_password => 'root',
    require       => Exec['apt-get update'],
}

mysql::grant { $mysql_db:
    mysql_privileges     => 'ALL',
    mysql_db             => $mysql_db,
    mysql_user           => $mysql_user,
    mysql_password       => $mysql_pass,
    mysql_host           => $mysql_host,
    mysql_grant_filepath => '/home/vagrant/puppet-mysql',
}

package { 'phpmyadmin':
    require => Class[ 'mysql' ],
}

apache::vhost { 'phpmyadmin':
    server_name => false,
    docroot     => '/usr/share/phpmyadmin',
    port        => $pma_port,
    priority    => '10',
    require     => Package['phpmyadmin'],
    template    => 'vagrantee/apache/vhost.conf.erb',
}

class { 'composer':
    require => [ Class[ 'php' ], Package[ 'curl' ] ]
}


composer::install { 'default':
    path    => '/vagrant',
    require => Class[ 'composer' ]
}

class { 'symfony':
  db_name  => $mysql_db,
  db_user  => $mysql_user,
  db_pass  => $mysql_pass,
}

/* optimize symfony AppKernel */
symfony::patch { 'vagrantee':}

stage { 'custom': }
Stage['main'] -> Stage['custom']

class { 'custom':
  stage => custom
}
