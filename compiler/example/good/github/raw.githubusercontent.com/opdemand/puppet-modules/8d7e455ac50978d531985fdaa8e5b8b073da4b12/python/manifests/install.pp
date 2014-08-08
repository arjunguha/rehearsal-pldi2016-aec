class python::install {

  # define local vars
  $username = "$python::params::username"
  $group = "$python::params::group"
  $repository_path = "$python::params::repository_path"
  $virtualenv_path = "$python::params::repository_path/venv"
  $upstart_template_path = "/var/cache/opdemand/upstart/$python::params::app_name"
  
  # define package names
  $pip_package = "python-pip"
  $virtualenv_package = "python-virtualenv"
  
  # install base python packages
  $packages = [ $pip_package, $virtualenv_package ]
  package { $packages:
    ensure => present,
  }
  
  # init virtual env
  exec { "virtualenv::init":
    command => "sudo -u $username virtualenv $virtualenv_path --distribute",
    cwd => $repository_path,
    path => ["/sbin", "/bin", "/usr/bin", "/usr/local/bin"],
    user => $username,
    group => $group,
    require => Package[$virtualenv_package],
    # only run if venv doesn't exist
    creates => $virtualenv_path,
  }

  # manage virtualenv directory
  file { $virtualenv_path:
    ensure => directory,
    owner => $username,
    group => $group,
    mode => 750,
    require => [ Exec["virtualenv::init"], Vcsrepo[$repository_path] ],
  }

  # create define for upstart template installation
  define upstart_template () {
    file { "/var/cache/opdemand/$name":
      source => "puppet:///modules/python/$name",
    }
  }

  # install upstart templates
  $templates = [ "master.conf.erb", "process_master.conf.erb", "process.conf.erb"]
  upstart_template { $templates: }
  
}
