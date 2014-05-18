class mysql (
  $module_root = 'puppet:///modules/mysql/',
  $packages = [
    'mysql-common',
    'mysql-server'
  ],
  $conf_files = [
    'conf.d/char.cnf',
    'conf.d/innodb.cnf',
  ],
  $password = 'password',
  $hostname = 'host.example.com',
  $local_only = true,
  $create_aegir_user = false,
  $aegir_user = '',
  $aegir_password = '',
  $aegir_host = 'aegir.example.com',
) {
  package { $packages:
    ensure => installed,
    # We need to have innodb settings on before we install
    require => File['/etc/mysql/conf.d/innodb.cnf']
  }

  service { mysql:
    enable    => true,
    ensure    => running,
    subscribe => Package['mysql-server'],
  }

  # Set mysql password for admin.
  exec { 'mysqladmin password':
    unless => "mysqladmin -uroot -p${password} status",
    path => ['/bin', '/usr/bin'],
    command => "mysqladmin -uroot password ${password}",
    require => Service['mysql'],
  }
  
  # Mysql is installed with anonymous access by default. Let's change that.
  exec { 'mysql-remove-anonymous':
    onlyif => 'mysqladmin -ubingoberra status',
    path => ['/bin', '/usr/bin'],
    command => "echo \"DROP USER ''@'localhost'; DROP USER ''@'${hostname}';\" | mysql -uroot -p${password}",
    require => [Service['mysql'], Exec['mysqladmin password']],
  }

  file { "/etc/mysql":
    ensure => directory
  }

  file { "/etc/mysql/conf.d":
    ensure => directory
  }


  define conf_file() {
    file { "/etc/mysql/${name}":
      owner => root,
      group => root,
      mode => 0444,
      source => "puppet:///modules/mysql/${name}",
      require => [File["/etc/mysql"],File["/etc/mysql/conf.d"]]
    }
  }

  conf_file { $conf_files:
  }

  if ! $local_only {
    # A more open version of my.cnf
    # @todo make this into a template.
    file { '/etc/mysql/dbnode-my.cnf':
      owner  => root,
      group  => root,
      mode   => '0444',
      source => 'puppet:///modules/mysql/dbnode-my.cnf',
      path   => '/etc/mysql/my.cnf',
      require => Package['mysql-server'],
      notify => Service['mysql']
    }

    if $create_aegir_user {
      exec { 'mysql-create-aegir-user':
        unless => "echo 'use mysql;select user from user;' | mysql -uroot -ppassword | grep ${aegir_user} > /dev/null",
        path => ['/bin', '/usr/bin'],
        command => "echo \"CREATE USER ${aegir_user} IDENTIFIED BY '${aegir_password}'; GRANT ALL PRIVILEGES ON *.* TO '${aegir_user}'@'${aegir_host}' IDENTIFIED BY '${aegir_password}' WITH GRANT OPTION;\" | mysql -uroot -p${password}",
        require => Service['mysql']
      }
    }
  }
}
