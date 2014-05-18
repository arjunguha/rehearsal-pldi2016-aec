class clojure::service {

  # local variables
  $repository_path = $clojure::params::repository_path
  $app_name = $clojure::params::app_name
  
  service { $app_name:
    ensure => running,
    provider => upstart,
    require => [ Class[Clojure::Install], Class[Clojure::Config], Class[Clojure::Deps] ],
    subscribe => Vcsrepo[$repository_path],
  }

}
