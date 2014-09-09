class clojure::install {

  # define local vars
  $username = "$clojure::params::username"
  $group = "$clojure::params::group"
  $repository_path = "$clojure::params::repository_path"
  $app_name = "$clojure::params::app_name"
  $upstart_template_path = "/var/cache/opdemand/upstart/$app_name"  
  $packages = [ "leiningen" ]
  
  package { $packages:
        ensure => latest,
  }

  # create define for upstart template installation
  define upstart_template () {
    file { "/var/cache/opdemand/$name":
      source => "puppet:///modules/clojure/$name",
    }
  }
  
  # install upstart templates
  $templates = [ "master.conf.erb", "process_master.conf.erb", "process.conf.erb"]
  upstart_template { $templates: }
  
}
