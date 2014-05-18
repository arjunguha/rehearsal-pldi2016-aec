class custom::install {

  # local variables
  $repository_path = $custom::params::repository_path
  $username = $custom::params::username
  $group = $custom::params::group
  
  # create define for upstart template installation
  define upstart_template () {
    file { "/var/cache/opdemand/$name":
      source => "puppet:///modules/custom/$name",
    }
  }
  
  # install upstart templates
  $templates = [ "master.conf.erb", "process_master.conf.erb", "process.conf.erb"]
  upstart_template { $templates: }
  
}
