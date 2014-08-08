
class democonfig {
  file {
    "/var/lib/jenkins/config.xml" :
      owner  => jenkins,
      group  => nogroup,
      ensure => file,
        require => [
                    Class['jenkins::package'],
        ],
      notify => Service['jenkins'],
      source => "puppet:///modules/democonfig/config.xml";
  }
}
