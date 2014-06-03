class rails::install {

  require rails::params

  $packages = [ "curl", "openssl", "ruby1.9.1", "ruby1.9.1-dev", "build-essential", "libsqlite3-ruby1.9.1", "libsqlite3-dev", "rubygems", "libv8-dev"]
  $gems = [ "bundler", "rails", "sinatra", "therubyracer", "rake", "coffee-rails", "sass-rails", "uglifier", "jquery-rails", "pg", "thin", "activerecord"]
  $db_packages = $rails::params::database_type ? {
    postgresql => [ "libpq-dev" ],
  }

  # install framework database packages
  package { $db_packages:
      ensure => latest,
  }

  # install framework packages
  package { $packages:
      ensure => latest,
      require => Package[$db_packages],
  }

  # install gems
  package { $gems:
      provider => "gem",
      ensure => latest,
      require => Package[$packages],
  }

  # bundle install
  exec { "sudo -u $rails::params::username bundle install":
    path => $path,
    cwd => "$rails::params::repository_path",
    user => "$rails::params::username",
    group => "$rails::params::group",
    require => Package["bundler"],
    subscribe => Vcsrepo[$rails::params::repository_path],
  }

  # override databases.rake to allow `rake db:create:all` to target remote databases
  file { "/usr/lib/ruby/gems/1.8/gems/activerecord-3.2.3/lib/active_record/railties/databases.rake":
    ensure => present,
    owner => "root",
    group => "root",
    mode => 0644,
    source => "puppet:///modules/rails/databases.rake",
    require => Package["activerecord"],
  }
  
}
