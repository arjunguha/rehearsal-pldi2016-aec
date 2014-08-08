class dev_rails_stack(
  $ruby_version = '1.9.3-p125',
  $bundler      = true,
  $mysql        = true,
  $mongodb      = false,
  $postgresql   = false,
  $redis        = false) {

  # Dependencies

  class { 'upgrade_distro': }
  
  class { 'base_packages':
    require => Class['upgrade_distro'],
  }
  
  class { 'virtualbox_guest_additions': 
    require => Class['base_packages'],
  }

  # Ruby

  class { 'rbenv':
    user      => 'vagrant',
    compile   => true,
    version   => $ruby_version,
    require   => Class['virtualbox_guest_additions'],
  }

  # Bundler

  if $bundler {
    exec { 'gem install bundler --no-ri --no-rdoc && echo "0"':
      path    => '/home/vagrant/.rbenv/shims:/home/vagrant/.rbenv/bin:/bin:/usr/bin:/usr/sbin',
      user    => 'vagrant',
      creates => '/home/vagrant/.rbenv/shims/bundle',
      require => Class['rbenv'],
    }
  }

  # MySQL

  if($mysql) {
    class { 'mysql': 
      require => Class['virtualbox_guest_additions'],
    }

    class { 'mysql::server':
      require => Class['virtualbox_guest_additions'],
      config_hash => {
        'root_password' => 'root'
      }
    }

    package { 'libmysqlclient-dev' :
      ensure => present,
      require => Class['mysql::server'],
    }

    mysql::db { 'development':
      user     => 'development',
      password => 'development',
      host     => 'localhost',
      grant    => ['all'],
      require  => Class['virtualbox_guest_additions'],
    }

    file { '/vagrant/config/database.yml':
      ensure  => file,
      content => template('dev_rails_stack/database.yml.erb'),
      require => Class['virtualbox_guest_additions'],
    }
  }

  # MongoDB

  if($mongodb) {
    package { 'mongodb':
      ensure  => present,
      require => Class['virtualbox_guest_additions'],
    }
  }

  # Postgres

  if($postgresql) {
    package { 'postgresql':
      ensure  => present,
      require => Class['virtualbox_guest_additions'],
    }
    package { 'postgresql-server-dev-all':
      ensure  => present,
      require => Package['postgresql']
    }
  }

  # Redis

  if($redis) {
    package { 'redis-server':
      ensure => present,
      require => Class['virtualbox_guest_additions'],
    }
  }
}
