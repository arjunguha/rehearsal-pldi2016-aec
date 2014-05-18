class rvm_install {
  include rvm
  if $rvm_installed == "true" {
    rvm_system_ruby {
      'ruby-1.9.3-p0':
        ensure => 'present',
        #unless => 'ls /usr/local/rvm/rubies/ruby-1.9.3-p0/bin/ruby',
        default_use => true;
    }
    rvm_gemset {
      "ruby-1.9.3-p0@test":
        ensure => present,
        require => Rvm_system_ruby['ruby-1.9.3-p0'];
    }
    rvm_gem {
      'ruby-1.9.3-p0@test/bundler':
        ensure => '1.0.21',
        require => Rvm_gemset['ruby-1.9.3-p0@test'];
    }
  }
}

class web {
  package { "rails-build-dependencies":
    ensure => installed,
    name => [
      "build-essential",
      "zlib1g-dev",
      "sqlite3",
      "libsqlite3-dev"
    ]
  }
  include rvm_install
  include rabbit_install
  include couchdb_install
  include riak_install
}
