class ruby::install {

  # define local vars
  $username = "$ruby::params::username"
  $group = "$ruby::params::group"
  $repository_path = "$ruby::params::repository_path"
  $upstart_template_path = "/var/cache/opdemand/upstart/$ruby::params::app_name"
  
  # install base ruby packages
  $packages = [ "ruby1.9.1", "ruby1.9.1-dev", "build-essential", "ruby-bundler" ]  # NOTE: bundler will install ruby1.8
  package { $packages:
    ensure => present,
  }

  # install ruby library packages (required by some gems)
  $library_packages = [ "libsqlite3-ruby1.9.1", "libxml-ruby1.9.1", "libactiverecord-ruby1.9.1" ]  
  package { $library_packages:
    ensure => present,
  }  
  
  # install ruby1.9.1 as default (actually 1.9.2 on ubuntu 11.10)
  exec { "ruby1.9.2-runtime":
    command => "update-alternatives --set ruby /usr/bin/ruby1.9.1",
    user => "root",
    group => "root",
    path => ["/sbin", "/bin", "/usr/bin", "/usr/sbin", "/usr/local/bin"],
    require => Package["ruby1.9.1"],
    unless => "ruby -v | grep 1.9.",
  }

  # install ruby1.9.1 gem command as default
  exec { "ruby1.9.2-gem":
    command => "update-alternatives --set gem /usr/bin/gem1.9.1",
    user => "root",
    group => "root",
    path => ["/sbin", "/bin", "/usr/bin", "/usr/sbin", "/usr/local/bin"],
    require => [ Package["ruby1.9.1"], Exec["ruby1.9.2-runtime"] ],
    unless => "gem -v | grep 1.3.7",
  }
  
  # create define for upstart template installation
  define upstart_template () {
    file { "/var/cache/opdemand/$name":
      source => "puppet:///modules/ruby/$name",
    }
  }

  # install upstart templates
  $templates = [ "master.conf.erb", "process_master.conf.erb", "process.conf.erb"]
  upstart_template { $templates: }
  
}
