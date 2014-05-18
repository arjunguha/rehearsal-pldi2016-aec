class ceilometer (
  $verbose                  = 'True',
  $debug                    = 'True',
  $metering_api_port        = 9000,
  $database_connection      = 'mongodb://localhost:27017/ceilometer',
  $auth_host                = 'localhost',
  $auth_port                = 35357,
  $auth_protocol            = 'https',
  $auth_user                = 'ceilometer',
  $auth_password            = 'svcp4ss',
  $auth_tenant_id           = '',
  $auth_tenant_name         = 'service',
  $auth_url                 = 'http://localhost:5000',
  $periodic_interval        = 600,
  $control_exchange         = 'ceilometer',
  $metering_secret          = 'Changem3',
  $metering_topic           = 'metering',
  $nova_control_exchange    = 'nova',
  $glance_control_exchange  = 'nova',
  $glance_registry_host     = 'localhost',
  $glance_registry_port     = 9191,
  $cinder_control_exchange  = 'cinder',
  $quantum_control_exchange = 'quantum',
  $rabbit_host              = 'localhost',
  $rabbit_port              = 5672,
  $rabbit_user              = 'guest',
  $rabbit_password          = 'guest',
  $rabbit_virtual_host      = '/'
) {
  include ceilometer::params

  require 'git'

  Vcsrepo['ceilometer'] -> Ceilometer_config<||>

  validate_re($database_connection, '(sqlite|mysql|posgres)|mongodb:\/\/(\S+:\S+@\S+\/\S+)?')

  case $database_connection  {
    /mysql:\/\/\S+:\S+@\S+\/\S+/: {
      $backend_package = 'python-mysqldb'
    }
    /postgres:\/\/\S+:\S+@\S+\/\S+/: {
      $backend_package = 'python-psycopg2'
    }
    /mongodb:\/\/(\S+:\S+@|)\S+\/\S+/: {
      $backend_package = 'python-pymongo'
    }
    /sqlite:\/\//: {
      $backend_package = 'python-pysqlite2'
    }
    default: {
      fail('Unsupported backend configured')
    }
  }

  package {'ceilometer-backend-package':
    name   => $backend_package,
    ensure => present
  }

  user {'ceilometer':
    comment => 'Ceilometer user',
    home    => $::ceilometer::params::install_dir,
    shell   => '/bin/bash',
    groups  => ['libvirtd', 'nova']
  }

  group {'ceilometer':
    require => User['ceilometer']
  }

  $file_requires = [Vcsrepo['ceilometer'], User['ceilometer'], Group['ceilometer']]

  file {'ceilometer-etc':
    name    => '/etc/ceilometer',
    ensure  => directory,
    owner   => $::ceilometer::params::user,
    group   => 'root',
    mode    => 660,
    require => $file_requires
  }

  file {'ceilometer-config':
    name    => '/etc/ceilometer/ceilometer.conf',
    ensure  => present,
    owner   => $::ceilometer::params::user,
    group   => 'root',
    mode    => 660,
    require => $file_requires
  }

  file {'ceilometer-var':
    name    => '/var/log/ceilometer',
    ensure  => directory,
    owner   => $::ceilometer::params::user,
    group   => $::ceilometer::params::group,
    mode    => 660,
    require => $file_requires
  }

  ceilometer_config {
    'DEFAULT/debug':                    value => $debug;
    'DEFAULT/verbose':                  value => $verbose;

    'DEFAULT/database_connection':      value => $database_connection;

    'DEFAULT/os_auth_url':              value => $auth_url;
    'DEFAULT/os_username':              value => $auth_user;
    'DEFAULT/os_password':              value => $auth_password;
    'DEFAULT/os_tenant_name':           value => $auth_tenant_name;

    'DEFAULT/auth_host':                value => $auth_host;
    'DEFAULT/auth_port':                value => $auth_port;
    'DEFAULT/auth_protocol':            value => $auth_protocol;

    'DEFAULT/periodic_interval':        value => $periodic_interval;
    'DEFAULT/control_exchange':         value => $control_exchange;
    'DEFAULT/metering_secret':          value => $metering_secret;
    'DEFAULT/metering_topic':           value => $metering_topic;
    'DEFAULT/nova_control_exchange':    value => $nova_control_exchange;
    'DEFAULT/glance_control_exchange':  value => $glance_control_exchange;
    'DEFAULT/glance_registry_host':     value => $glance_registry_host;
    'DEFAULT/glance_registry_port':     value => $glance_registry_port;
    'DEFAULT/cinder_control_exchange':  value => $cinder_control_exchange;
    'DEFAULT/quantum_control_exchange': value => $quantum_control_exchange;

    'DEFAULT/rabbit_host':              value => $rabbit_host;
    'DEFAULT/rabbit_port':              value => $rabbit_port;
    'DEFAULT/rabbit_user':              value => $rabbit_user;
    'DEFAULT/rabbit_password':          value => $rabbit_password;
    'DEFAULT/rabbit_virtual_host':      value => $rabbit_virtual_host;
  }

  if $auth_tenant_id {
    ceilometer_config {
      'DEFAULT/os_tenant_id':             value => $auth_tenant_id;
    }
  }

  vcsrepo {'ceilometer':
    name     => $::ceilometer::params::install_dir,
    owner    => $::ceilometer::params::user,
    group    => $::ceilometer::params::group,
    ensure   => present,
    provider => git,
    require  => [Package['git'], Package['ceilometer-backend-package'], User['ceilometer']],
    source   => $::ceilometer::params::source,
    revision => $::ceilometer::params::revision
  }

  exec {'ceilometer-install':
    name    => 'python setup.py develop',
    cwd     => $::ceilometer::params::install_dir,
    path    => [$::ceilometer::params::install_dir, '/usr/bin', '/usr/sbin'],
    require => Vcsrepo['ceilometer']
  }
}
